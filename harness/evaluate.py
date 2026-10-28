#!/usr/bin/env python3
"""The evaluation of one entry, in the harness order (TRUSTED RUNTIME; v3 §9.3 as amended by
V4-A1, V4-A2, V4-15, V4-A9).

  python3 -I harness/evaluate.py cert  --entry ENTRY --org ORG --work WORK --out CERT.json [--nanoda]
                                       [--season harness/season.toml]
  python3 -I harness/evaluate.py bench --entry ENTRY --cert CERT.json --work WORK --out RESULT.json
                                       [--season harness/season.toml] [--parts PARTS]
  python3 -I harness/evaluate.py all   --entry ENTRY --org ORG --work WORK --out RESULT.json [...]

ENTRY: `claim.json` (the declared numbers: `error`, `completeness_error` as "a/b" strings, `qV`,
`fuel_base`, `fuel_per_word` as integers), `lean/*.lean` (the solution; `lean/Solution.lean`
defines `RecursionFast.Challenge.submission` and proves `RecursionFast.Challenge.certified`), and
`prover/*.s`. ORG: the organiser's checkout, built, with its package tree, its olean manifest
(`ORG/.lake/rf/manifest.sha256`) and import allowlist (`ORG/.lake/rf/allowlist.txt`) written by
`harness/org-setup.sh` before any entry code ran.

The certificate job (`cert`; deterministic, any machine with the package tree), every Lean step
capped by the season file's `[certificate]` (V4-A9; a breach is the entry's REJECT, except the
kernel's, Q12):
  1. render the challenge from the organiser's stub and the claim (the entry supplies no stub);
  2. the source rule on the entry's Lean files (no elaboration-time code);
  3. the one build (V4-A9): in a fresh tree, in the sandbox, the comparator's targets (the
     challenge and the solution's import closure; entry modules that `Solution` does not import are
     never built, Q7), within `build_s`;
  4. the comparator on that build (`scripts/bwrap-landrun.sh`; its `lake build` finds it up to
     date): it replays the exported proof of `certified` against the rendered statement in the
     Lean kernel, and in nanoda with `--nanoda` (the result says which kernels ran), within
     `kernel_s`; the build's artifacts must be unchanged by it, so the gate and the badge read the
     artifacts the kernel's exports were made from; the organiser's oleans are checked against the
     manifest before the build and after the badge build (step 6), and the result records the
     manifest's and the allowlist's hashes (`environment`);
  5. the gate (rules 1–8, badge fields V, P, ext) in the sandbox, within `gate_s`;
  6. the badge executable `verify` rendered from `harness/badge/*.lean.in` and built in the sandbox
     in that tree within `badge_s`; it must neither build nor change an entry module (the badge's
     import closure lies inside the verified one); the organiser's `chaincheck` copied beside it.
  Status: `ok` (certified), `provisional` (everything builds and the only failures are an
  incomplete certificate: the comparator's verdict and gate rule 1's `sorryAx`), `reject`. The
  result records each capped step's seconds (`build_s`, `comparator_s`, `gate_s`, `badge_s`) and
  each kernel run's memory peak (`kernel_runs`, sampled while it runs: review E-ks).
The benchmark job (`bench`; the GitHub-hosted runner): `harness/run-benchmark.py` with the badge.
Verdict: ACCEPT (certificate ok, benchmark pass), PROVISIONAL (certificate provisional, benchmark
pass; never ranked, V4-15, its numbers marked uncomparable), REJECT (anything else).
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from rfh.sandbox import PeakWatch, Sandbox, kill_unit, memcap, scope_oom  # noqa: E402

TIMEOUT = 300           # an organiser command: render, source rule, manifest check
PART_S = 1680           # the benchmark job (28 min): the outer bound of its capped steps (V4-A9, V4-A11)
CHALLENGE_MODULE, SOLUTION_MODULE = "Challenge", "Solution"


class Reject(Exception):
    pass


class HarnessError(Exception):
    """A failure of the organiser's side (toolchain, comparator), not the entry's: verdict ERROR."""


def sh(cmd, cwd=None, env=None, timeout=TIMEOUT, log=None):
    """Run a trusted command (outside the sandbox); its output goes to `log`."""
    with open(log, "ab") if log else open(os.devnull, "wb") as f:
        return subprocess.run(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=timeout).returncode


def lean_prefix(org):
    return subprocess.run(["lean", "--print-prefix"], cwd=org, capture_output=True, text=True, check=True).stdout.strip()


def packages_dir(org):
    m = json.load(open(os.path.join(org, "lake-manifest.json")))
    return os.path.realpath(os.path.join(org, m.get("packagesDir") or ".lake/packages"))


def entry_modules(entry):
    d = os.path.join(entry, "lean")
    files = sorted(f for f in os.listdir(d) if f.endswith(".lean")) if os.path.isdir(d) else []
    for f in files:
        p = os.path.join(d, f)
        if os.path.islink(p) or not os.path.isfile(p):
            raise Reject(f"lean/{f} is not a regular file")
    if f"{SOLUTION_MODULE}.lean" not in files:
        raise Reject(f"lean/{SOLUTION_MODULE}.lean is missing")
    return files


def mkfresh(t, org, entry, challenge, files):
    """A fresh tree `t`: the rendered challenge, the entry's Lean files, a lakefile and manifest that
    require ORG by path; every module root fresh (no organiser or package module shadowed)."""
    os.makedirs(os.path.join(t, "challenge"))
    os.makedirs(os.path.join(t, "submission"))
    shutil.copy(os.path.join(org, "lean-toolchain"), t)
    shutil.copy(challenge, os.path.join(t, "challenge", f"{CHALLENGE_MODULE}.lean"))
    for f in files:
        shutil.copy(os.path.join(entry, "lean", f), os.path.join(t, "submission", f))
    pk = packages_dir(org)
    dirs = [os.path.join(org, ".lake/build/lib/lean"), os.path.join(lean_prefix(org), "lib/lean")]
    dirs += [os.path.join(pk, p, ".lake/build/lib/lean") for p in os.listdir(pk)]
    mods = [f[:-5] for f in files]
    for r in sorted({m.split(".")[0] for m in mods + [CHALLENGE_MODULE]}):
        for d in dirs:
            if os.path.isdir(os.path.join(d, r)) or os.path.exists(os.path.join(d, r + ".olean")):
                raise Reject(f"module root {r} exists in {d}")
    q = lambda xs: "[" + ", ".join(json.dumps(x) for x in xs) + "]"  # noqa: E731
    lib = lambda n, src, roots: f'[[lean_lib]]\nname = "{n}"\nsrcDir = "{src}"\nroots = {q(roots)}\n'  # noqa: E731
    with open(os.path.join(t, "lakefile.toml"), "w") as f:
        f.write(f'name = "rfentry"\npackagesDir = {json.dumps(pk)}\n[[require]]\nname = "RecursionFast"\n'
                f'path = {json.dumps(org)}\n' + lib("RFChallenge", "challenge", [CHALLENGE_MODULE])
                + lib("RFSubmission", "submission", mods))
    m = json.load(open(os.path.join(org, "lake-manifest.json")))
    for p in m["packages"]:
        p["inherited"] = True
    m["packages"].insert(0, {"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
                             "inherited": False, "dir": org, "configFile": "lakefile.toml"})
    m["name"], m["packagesDir"] = "rfentry", pk
    json.dump(m, open(os.path.join(t, "lake-manifest.json"), "w"), indent=1)


def artifacts(t):
    """sha256 of the build artifacts of the tree `t` (no link or special file allowed)."""
    out = {}
    b = os.path.join(t, ".lake", "build")
    for d in ("lib/lean", "ir"):
        for dp, dns, fns in os.walk(os.path.join(b, d)):
            for fn in fns:
                p = os.path.join(dp, fn)
                if os.path.islink(p) or not os.path.isfile(p):
                    raise Reject(f"build artifact {p} is not a regular file")
                if fn.endswith((".olean", ".olean.server", ".olean.private", ".ir", ".c")):
                    out[os.path.relpath(p, b)] = hashlib.sha256(open(p, "rb").read()).hexdigest()
    return out


class Org:
    """The organiser side: checkout, toolchain, packages, manifest, allowlist, tool binaries."""

    def __init__(self, org):
        self.dir = os.path.abspath(org)
        self.prefix = lean_prefix(self.dir)
        self.packages = packages_dir(self.dir)
        rf = os.path.join(self.dir, ".lake", "rf")
        self.manifest, self.allowlist = os.path.join(rf, "manifest.sha256"), os.path.join(rf, "allowlist.txt")
        self.tools = os.path.join(REPO, "harness", "lean-tools", ".lake", "build", "bin")
        for p in (self.manifest, self.allowlist, os.path.join(self.tools, "gate"), os.path.join(self.tools, "chaincheck")):
            if not os.path.exists(p):
                raise SystemExit(f"evaluate: {p} missing (run harness/org-setup.sh first)")

    def ro_roots(self, *more):
        """What a sandboxed Lean step may read: the system's /usr, the toolchain, the organiser
        checkout and packages, and `more`."""
        return ("/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache", self.prefix, self.dir, self.packages) + more

    def manifest_ok(self, log):
        return sh([sys.executable, "-I", os.path.join(REPO, "scripts", "olean-manifest.py"), "check", "--org", self.dir,
                   self.manifest], log=log) == 0

    def environment(self):
        """What the certificate was checked against (review D-trim m-4): the organiser's commit and the
        hashes of its olean manifest and import allowlist, which came with the restored cache."""
        sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()  # noqa: E731
        commit = subprocess.run(["git", "-C", self.dir, "rev-parse", "HEAD"], capture_output=True, text=True,
                                timeout=TIMEOUT).stdout.strip() or None
        return {"core_commit": commit, "manifest_sha256": sha(self.manifest), "allowlist_sha256": sha(self.allowlist)}


def sandboxed(org, cmd, tree, log, rw=(), mem="12G", env=None, timeout=TIMEOUT, extra=()):
    """Run `cmd` in the sandbox with `tree` visible at its own path (read-only unless in `rw`)."""
    binds = [("ro", tree, tree)] + [("rw", p, p) for p in rw]      # parents first: rw paths lie in the tree
    e = {"PATH": f"{org.prefix}/bin:/usr/bin:/bin", "HOME": tree, "LAKE_NO_CACHE": "1"}
    e.update(env or {})
    with open(log, "ab") as f:
        sb = Sandbox(cmd, binds, mem, env=e, cwd=tree, stdout=f, stderr=subprocess.STDOUT,
                     extra_ro_root=org.ro_roots(*extra))
        try:
            return sb.proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            return "timeout"
        finally:
            sb.kill()


def cert_job(a):
    org = Org(a.org)
    caps = tomllib.load(open(a.season, "rb"))["certificate"]
    work = os.path.abspath(a.work)
    os.makedirs(work, exist_ok=False)
    entry = os.path.abspath(a.entry)
    res = {"stage": "certificate", "kernels": [], "reasons": [], "provisional_reasons": [], "caps": caps}
    logs = {k: os.path.join(work, f"{k}.log") for k in ("render", "source-rule", "build", "gate", "badge", "manifest")}
    try:
        files = entry_modules(entry)
        # 1. the challenge
        challenge = os.path.join(work, f"{CHALLENGE_MODULE}.lean")
        if sh([sys.executable, "-I", os.path.join(HERE, "render-challenge.py"), os.path.join(HERE, "challenge",
               "Challenge.lean.in"), os.path.join(entry, "claim.json"), challenge], log=logs["render"]):
            raise Reject("claim does not render: " + open(logs["render"]).read()[-300:])
        res["claim"] = json.load(open(os.path.join(entry, "claim.json")))
        # 2. the source rule
        sr = os.path.join(work, "sr")
        os.makedirs(sr)
        for f in files:
            shutil.copy(os.path.join(entry, "lean", f), sr)
        if sh([sys.executable, "-I", os.path.join(REPO, "scripts", "source-rule.py"), sr], log=logs["source-rule"]):
            raise Reject("source rule: " + open(logs["source-rule"]).read()[-600:])
        # 3. the one build (V4-A9), in a fresh tree, in the sandbox: exactly the comparator's targets,
        # the challenge and the solution's import closure; an entry module that `Solution` does not
        # import is never built by the harness (Q7). The manifest is checked here, on the restored
        # environment, and once more after the badge build, which covers every step in between.
        res["environment"] = org.environment()
        if not org.manifest_ok(logs["manifest"]):
            raise HarnessError("the organiser's build does not match its olean manifest")
        tree = os.path.join(work, "tree")
        mkfresh(tree, org.dir, entry, challenge, files)
        lake = os.path.join(org.prefix, "bin", "lake")
        os.makedirs(os.path.join(tree, ".lake"))
        t0 = time.monotonic()
        rc = sandboxed(org, [lake, "build", f"+{CHALLENGE_MODULE}", f"+{SOLUTION_MODULE}"], tree, logs["build"],
                       rw=(os.path.join(tree, ".lake"),), timeout=caps["build_s"])
        res["build_s"] = round(time.monotonic() - t0, 1)
        if rc == "timeout":
            raise Reject(f"the solution did not build within build_s = {caps['build_s']} s (V4-A9)")
        if rc != 0:
            raise Reject(f"the solution does not build ({rc}): " + open(logs["build"], errors="replace").read()[-400:])
        built = artifacts(tree)
        # 4. the comparator on that build: its own `lake build` of the two targets finds them up to
        # date, and it exports them and replays the proofs in the kernel
        home = os.environ.get("COMPARATOR_HOME", "")
        cmp_bin = os.path.join(home, ".lake", "build", "bin", "comparator")
        export = os.environ.get("COMPARATOR_LEAN4EXPORT",
                                os.path.join(home, ".lake/packages/lean4export/.lake/build/bin/lean4export"))
        if not (os.access(cmp_bin, os.X_OK) and os.access(export, os.X_OK)):
            raise HarnessError("the comparator or lean4export is missing (scripts/tools.env)")
        env = dict(os.environ, COMPARATOR_LANDRUN=os.path.join(REPO, "scripts", "bwrap-landrun.sh"),
                   COMPARATOR_LEAN4EXPORT=export, RF_LANDRUN_MINIMAL="1",
                   RF_LANDRUN_RO=":".join(org.ro_roots(home, os.path.dirname(export))))

        def kernel_run(kernel, mem):
            """One comparator run in its own memory-capped scope (Q12), within `kernel_s`: `lean`
            checks with the Lean kernel alone; `nanoda` adds nanoda (the comparator then also re-runs
            the Lean kernel). Its outcome: ok, rejected, over budget (the scope was killed for
            memory) or timeout."""
            cfg = {"challenge_module": CHALLENGE_MODULE, "solution_module": SOLUTION_MODULE,
                   "theorem_names": ["RecursionFast.Challenge.certified"],
                   "definition_names": ["RecursionFast.Challenge.submission"],
                   "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "enable_nanoda": kernel == "nanoda"}
            json.dump(cfg, open(os.path.join(tree, f"config-{kernel}.json"), "w"))
            e = dict(env)
            if kernel == "nanoda":
                e["COMPARATOR_NANODA"] = os.environ["COMPARATOR_NANODA"]
                e["RF_LANDRUN_RO"] += ":" + os.path.dirname(os.path.abspath(os.environ["COMPARATOR_NANODA"]))
            unit, log = f"rf-cmp-{kernel}-{os.getpid()}", os.path.join(work, f"comparator-{kernel}.log")
            t0 = time.monotonic()
            watch = PeakWatch(unit)     # the peak of a run that ends normally (its scope is then collected)
            try:
                rc = sh(memcap(mem, unit) + ["lake", "env", cmp_bin, f"config-{kernel}.json"], cwd=tree, env=e, log=log,
                        timeout=caps["kernel_s"])
            except subprocess.TimeoutExpired:
                rc = "timeout"
                kill_unit(unit)
            finally:
                seen = watch.stop()
            oom, peak = scope_oom(unit)
            peak = max(filter(None, (peak, seen)), default=None)
            out = open(log, errors="replace").read()
            outcome = "ok" if rc == 0 else "over budget" if oom else "timeout" if rc == "timeout" else "rejected"
            return {"outcome": outcome, "exit": rc, "seconds": round(time.monotonic() - t0, 1), "cap": mem,
                    "peak_bytes": peak, "tail": out[-1500:]}

        # RB-m2: a run's exit code decides (the comparator runs outside the sandbox; its log also holds
        # the entry's build output, so no substring of it is trusted)
        lean = kernel_run("lean", a.cert_mem)
        res["kernel_runs"] = {"lean": lean}
        res["comparator_s"] = lean["seconds"]
        full = open(os.path.join(work, "comparator-lean.log"), errors="replace").read()
        if lean["outcome"] == "rejected" and f"Building {SOLUTION_MODULE}" not in full:
            # the comparator failed on the organiser's challenge, before it reached the solution (e.g.
            # a lean4export of another Lean: "incompatible header", CI run 39960437824)
            raise HarnessError("the comparator stopped before building the solution: " + lean["tail"][-600:])
        unchecked = lean["outcome"] in ("over budget", "timeout")     # Q12: the kernel's budget, not the entry
        budget = lambda r: f"cap {r['cap']}" + (f", peak {r['peak_bytes'] / 2 ** 30:.2f} GiB" if r["peak_bytes"] else "")  # noqa: E731
        res["kernels"] = ["lean"] if lean["outcome"] == "ok" else []
        if lean["outcome"] == "rejected":
            res["provisional_reasons"].append(f"comparator (Lean kernel): exit {lean['exit']}, the certificate does not check")
        elif lean["outcome"] == "over budget":
            res["provisional_reasons"].append(f"the Lean kernel ran over its memory budget ({budget(lean)}): "
                                              "the certificate is unchecked, not refuted")
        elif lean["outcome"] == "timeout":
            res["provisional_reasons"].append(f"the Lean kernel did not finish within kernel_s = {caps['kernel_s']} s: "
                                              "the certificate is unchecked")
        if not a.nanoda:
            res["second_kernel"] = "not run (no --nanoda): checked by the Lean kernel only (V4-A2)"
        elif lean["outcome"] != "ok":
            res["second_kernel"] = "not run: the Lean kernel did not accept"
        else:
            nan = kernel_run("nanoda", a.nanoda_mem)
            res["kernel_runs"]["nanoda"] = nan
            if nan["outcome"] == "ok":
                res["kernels"].append("nanoda")
                res["second_kernel"] = "nanoda: accepted"
            elif nan["outcome"] == "rejected":
                res["second_kernel"] = "nanoda: rejected"
                res["provisional_reasons"].append("nanoda rejected the certificate the Lean kernel accepted")
            else:      # over budget or timeout: no second check, the Lean kernel's verdict stands (V4-A2)
                res["second_kernel"] = f"nanoda: {nan['outcome']} ({budget(nan)}); checked by the Lean kernel only"
        # the binding (V4-A9): the artifacts the kernel's exports were read from are the build's, unchanged
        arts = artifacts(tree)
        diff = sorted(k for k in set(arts) | set(built) if built.get(k) != arts.get(k))
        if diff:
            raise Reject(f"the build changed during the comparator run ({len(diff)} artifacts, e.g. {diff[:3]}): "
                         "the comparator's check is not of this build")
        res["binding"] = (f"one build ({len(arts)} artifacts), read by the comparator, the gate and the badge build"
                          + ("; the kernel did not finish, so the entry stays provisional" if unchecked else ""))
        res["built_modules"] = sorted(k[len("lib/lean/"):-len(".olean")].replace("/", ".") for k in arts
                                      if k.startswith("lib/lean/") and k.endswith(".olean"))
        # 5. the gate, in the sandbox
        lp = subprocess.run([lake, "env", "printenv", "LEAN_PATH"], cwd=tree, capture_output=True, text=True,
                            timeout=TIMEOUT).stdout.strip()
        gate = os.path.join(org.tools, "gate")
        t0 = time.monotonic()
        rc = sandboxed(org, [gate, SOLUTION_MODULE, "RecursionFast.Challenge.certified", "--manifest", org.manifest,
                             "--computable", "RecursionFast.Challenge.submission", "--allowed-imports", org.allowlist,
                             "--badge-root", "RecursionFast.Challenge.submission"],
                       tree, logs["gate"], env={"LEAN_PATH": lp}, extra=(org.tools, os.path.dirname(org.manifest)),
                       timeout=caps["gate_s"])
        res["gate_s"] = round(time.monotonic() - t0, 1)
        if rc == "timeout":
            raise Reject(f"the gate did not finish within gate_s = {caps['gate_s']} s (V4-A9)")
        rejects = [l for l in open(logs["gate"], errors="replace").read().splitlines() if l.startswith("gate: REJECT")]
        res["gate"] = rejects or ["PASS"]
        open_cert = ("gate: REJECT closure uses sorryAx", "gate: REJECT non-standard axiom sorryAx")
        hard = [l for l in rejects if l not in open_cert]      # only an open certificate may be provisional
        if hard or (rc != 0 and not rejects):
            raise Reject("gate: " + "; ".join(hard[:5] or [f"exit {rc}"]))
        if rejects:
            res["provisional_reasons"].append("gate rule 1: the certificate's closure uses sorryAx")
        # 6. the badge
        badge = build_badge(org, tree, logs["badge"], caps["badge_s"], res)
        # Q7: the badge's import closure lies inside the verified one: its build adds no entry
        # module and changes no verified artifact
        after = {k: v for k, v in artifacts(tree).items() if "/RFBadge" not in "/" + k.split("/", 2)[-1]}
        moved = sorted(k for k in set(after) | set(arts) if after.get(k) != arts.get(k))
        if moved:
            raise Reject(f"the badge build built or changed entry modules outside the verified closure: {moved[:3]}")
        res["badge_dir"] = badge
        res["badge_sha256"] = {b: hashlib.sha256(open(os.path.join(badge, b), "rb").read()).hexdigest()
                               for b in os.listdir(badge)}
        res["status"] = "provisional" if res["provisional_reasons"] else "ok"
    except Reject as e:
        res["status"] = "reject"
        res["reasons"].append(str(e))
    except HarnessError as e:
        res["status"] = "error"
        res["reasons"].append(f"harness error: {e}")
    except subprocess.TimeoutExpired as e:      # only an organiser command raises it (entry steps return "timeout")
        res["status"] = "error"
        res["reasons"].append(f"harness error: an organiser command did not finish within {e.timeout} s: "
                              f"{' '.join(map(str, e.cmd))[:200] if e.cmd else ''}")
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"certificate: {res['status']} {res['reasons'] or res['provisional_reasons']}")
    return res


def build_badge(org, tree, log, timeout, res):
    """Render the badge executable `verify` into `tree` (`harness/badge/*.lean.in`, around the
    solution module) and build it in the sandbox within `timeout`, recording its duration as
    `res["badge_s"]`; returns the directory holding `verify` and the organiser's `chaincheck`."""
    bdir = os.path.join(tree, "badge")
    os.makedirs(bdir)
    for name in ("Common", "Verify"):
        src = open(os.path.join(HERE, "badge", f"{name}.lean.in")).read().replace("{{solution_module}}", SOLUTION_MODULE)
        open(os.path.join(bdir, f"RFBadge{name}.lean"), "w").write(src)
    with open(os.path.join(tree, "lakefile.toml"), "a") as f:
        f.write('\n[[lean_lib]]\nname = "RFBadge"\nsrcDir = "badge"\nroots = ["RFBadgeCommon"]\n'
                '\n[[lean_exe]]\nname = "verify"\nsrcDir = "badge"\nroot = "RFBadgeVerify"\n')
    # An executable links the compiled object of every module it imports. `org-setup.sh` built those
    # of the organiser's closure; the objects of other modules an entry imports are compiled here,
    # into the package tree, so its build directories are writable for this step. No entry code runs
    # in it (the entry's modules are loaded, not elaborated; gate rule 3 excludes load-time code),
    # and the olean manifest is checked afterwards.
    rw = [os.path.join(tree, ".lake"), os.path.join(org.dir, ".lake", "build")]
    rw += [os.path.join(org.packages, p, ".lake") for p in sorted(os.listdir(org.packages))
           if os.path.isdir(os.path.join(org.packages, p, ".lake"))]
    t0 = time.monotonic()
    rc = sandboxed(org, [os.path.join(org.prefix, "bin", "lake"), "build", "verify"], tree, log,
                   rw=tuple(rw), timeout=timeout)
    res["badge_s"] = round(time.monotonic() - t0, 1)
    if rc == "timeout":
        raise Reject(f"the badge did not build within badge_s = {timeout} s (V4-A9)")
    if rc != 0:
        raise Reject(f"badge build failed ({rc}): " + open(log, errors="replace").read()[-400:])
    if not org.manifest_ok(log):
        raise Reject("organiser .olean changed during the build, the comparator, the gate or the badge build")
    out = os.path.join(os.path.dirname(tree), "badge")
    os.makedirs(out)
    shutil.copy(os.path.join(tree, ".lake", "build", "bin", "verify"), out)
    shutil.copy(os.path.join(org.tools, "chaincheck"), out)
    return out


def bench_job(a, cert):
    cmd = [sys.executable, "-I", os.path.join(HERE, "run-benchmark.py"), "--season", a.season, "--entry", a.entry,
           "--badge", cert["badge_dir"], "--service", a.service, "--bench", a.bench, "--work", a.work, "--out", a.out]
    if cert["status"] == "provisional":
        cmd.append("--provisional")
    if a.parts:
        cmd += ["--parts", a.parts]
    # every step the entry controls is capped inside (season file); this bounds the organiser's own
    # steps, so that a part ends inside its 30-minute job (V4-A9)
    subprocess.run(cmd, timeout=PART_S)
    res = json.load(open(a.out))
    res["certificate"] = {k: cert.get(k) for k in ("status", "reasons", "provisional_reasons", "kernels", "second_kernel",
                                                   "kernel_runs", "binding", "gate", "badge_sha256", "claim",
                                                   "built_modules", "environment")}
    ok = res["benchmark"] == "pass"
    res["verdict"] = ("ACCEPT" if cert["status"] == "ok" else "PROVISIONAL") if ok and cert["status"] != "reject" else "REJECT"
    res["comparable"] = res["verdict"] == "ACCEPT" and not (res.get("stream") or {}).get("truncated")
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"VERDICT: {res['verdict']}")
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["cert", "bench", "all"])
    ap.add_argument("--entry", required=True)
    ap.add_argument("--org")
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--cert")
    ap.add_argument("--nanoda", action="store_true")
    ap.add_argument("--cert-mem", default="14G", help="memory cap of the comparator run with the Lean kernel")
    ap.add_argument("--nanoda-mem", default="14G", help="memory cap of the comparator run with nanoda")
    ap.add_argument("--season", default=os.path.join(HERE, "season.toml"))
    ap.add_argument("--service", default=os.path.join(REPO, "service", "target", "release", "rf-oracle"))
    ap.add_argument("--bench", default=os.path.join(REPO, "service", "target", "release", "rf-bench"))
    ap.add_argument("--parts")
    a = ap.parse_args()
    if a.mode == "bench":
        res = bench_job(a, json.load(open(a.cert)))
    else:
        out, work = a.out, a.work
        a.out, a.work = (out if a.mode == "cert" else out + ".cert.json"), (work if a.mode == "cert" else work + "/cert")
        if a.mode == "all":
            os.makedirs(work)
        cert = cert_job(a)
        if a.mode == "cert":
            return {"ok": 0, "provisional": 0, "reject": 1}.get(cert["status"], 2)
        a.out, a.work = out, work + "/bench"
        if cert["status"] in ("reject", "error"):
            verdict = "REJECT" if cert["status"] == "reject" else "ERROR"
            res = {"verdict": verdict, "comparable": False, "certificate": cert}
            json.dump(res, open(out, "w"), indent=1)
            print(f"VERDICT: {verdict}")
            return 1 if verdict == "REJECT" else 2
        res = bench_job(a, cert)
    return 0 if res["verdict"] in ("ACCEPT", "PROVISIONAL") else 1


if __name__ == "__main__":
    sys.exit(main())
