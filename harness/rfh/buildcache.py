"""The record's entry build, reused by later evaluations (TRUSTED RUNTIME; launch stage S5).

An entry that sets a record is usually the base of the next ones: the same Lean modules, a few
changed. The certificate job of an ACCEPTed entry exports the build outputs of its own modules
(`export`); the submissions bot caches that export only when the result becomes the new record;
a later certificate job restores the newest such cache into its fresh tree before the one build
(`restore`), and Lake rebuilds every module whose inputs changed. No entry run writes a cache.

What is exported and restored: for an entry module `M` (a file `lean/M.lean` of the entry), its
`lib/lean/M.{olean,olean.server,olean.private,ilean,ir,ir.sig,trace}` and `ir/M.{c,bc}`. Never the
rendered `Challenge` (it is rendered from each entry's claim and always built fresh, so the
comparator's challenge never comes from a cache), never an organiser or package module (they are
in the organiser's tree, not the entry's), never a badge module, never Lake's `.hash` files (Lake
recomputes them from the restored bytes), `.setup.json`, `.ltar` or compiled objects.

Nothing is restored unless the manifest's sha256 equals the one the caller passes, the record's
attested `certificate.entry_build.manifest_sha256` (launch R4 m4: the cache is bound to the record,
not to whoever wrote the cache store). A module is then restored only if (1) the cache was exported
at the same core commit, (2) the entry's `lean/M.lean` is byte-identical to the record's, and (3)
every file's sha256 equals that manifest, written by the record's harness after its last sandboxed
step. Lake then decides, on its own trace (source, imports' olean hashes, toolchain, options), whether `M` is up to date.

What this trusts (the residual): Lake does not rehash an up-to-date module's outputs, so a
restored module's olean and `.c` are the record's build outputs, not this entry's. The record's
certificate was checked on exactly those bytes (its kernel replay covered every declaration that
`certified` and `submission` depend on, and its gate and badge read the same files), and this
entry's comparator replays every declaration of the oleans again from an empty environment. The
kernel never reads `.c`: a restored module's `.c`, which the badge is compiled from, is trusted as
the record's run produced it, bound to the record by the attested manifest hash (the input
`expect`). What a cache adds is O-12's residual one step removed: compiled code (or an olean differing from its source) that
elaboration-time code in the record's build could have forged, which the source rule guards in
the record's run as it guards this entry's. The result records the restored modules.
"""
import hashlib
import json
import os
import shutil

SCHEMA = "recursion.fast/v4/entry-build-1"
MANIFEST = "manifest.json"
LIB_EXTS = ("olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig")
IR_EXTS = ("c", "bc")
MANIFEST_CAP = 16 << 20


def _sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def eligible(m):
    """An entry module whose outputs may be cached: not the rendered challenge, not a badge module."""
    return m != "Challenge" and not m.startswith("RFBadge")


def outputs(m):
    """The build outputs of the entry module `m`, relative to `.lake/build`; the trace last, so a
    module restored only in part has no trace and is rebuilt."""
    return [f"lib/lean/{m}.{e}" for e in LIB_EXTS] + [f"ir/{m}.{e}" for e in IR_EXTS] + [f"lib/lean/{m}.trace"]


def _put(src, dst, link=False):
    """Copy `src` to `dst`; with `link`, hard-link it where possible (the export only: nothing
    writes the tree after it, whereas a build writes a restored module's files in place)."""
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if link:
        try:
            return os.link(src, dst)
        except OSError:
            pass
    shutil.copyfile(src, dst)


def _regular(p):
    return os.path.isfile(p) and not os.path.islink(p)


def export(tree, files, out, core_commit):
    """Write the build outputs of the entry modules built in `tree` (`files`: the entry's
    `lean/*.lean` names) and their manifest to the new directory `out`; returns the summary that
    the certificate records (`manifest_sha256` binds the uploaded files to the attested result)."""
    build = os.path.join(tree, ".lake", "build")
    os.makedirs(out)
    mods, n, size = {}, 0, 0
    for f in files:
        m = f[:-len(".lean")]
        if not (eligible(m) and _regular(os.path.join(build, "lib", "lean", f"{m}.olean"))):
            continue        # not built: outside Solution's import closure (Q7)
        rec = {}
        for rel in outputs(m):
            p = os.path.join(build, rel)
            if not os.path.lexists(p):
                continue
            if not _regular(p):
                raise ValueError(f"build output {rel} is not a regular file")
            _put(p, os.path.join(out, rel), link=True)
            rec[rel] = _sha(p)
            n, size = n + 1, size + os.path.getsize(p)
        mods[m] = {"source_sha256": _sha(os.path.join(tree, "submission", f)), "files": rec}
    man = os.path.join(out, MANIFEST)
    json.dump({"schema": SCHEMA, "core_commit": core_commit, "modules": mods}, open(man, "w"), indent=1, sort_keys=True)
    return {"modules": len(mods), "files": n, "bytes": size, "manifest_sha256": _sha(man)}


def restore(src, tree, files, core_commit, key=None, expect=None):
    """Copy into `tree/.lake/build` the cached outputs of every entry module that passes the checks
    above; returns what the certificate records. A cache that is absent, unreadable, not the attested
    record's (`expect`, its manifest's sha256; None restores nothing) or from another core commit
    restores nothing (it is organiser data: it never fails an entry)."""
    res = {"key": key, "restored": [], "manifest_sha256": None, "expected_manifest_sha256": expect}
    man = os.path.join(src, MANIFEST)
    try:
        if not _regular(man) or os.path.getsize(man) > MANIFEST_CAP:
            res["note"] = "no manifest"
            return res
        res["manifest_sha256"] = _sha(man)
        if not expect or res["manifest_sha256"] != expect:
            res["note"] = "the cache is not the attested record's build (manifest sha256 differs or none was given)"
            return res
        m_all = json.load(open(man))
        if not core_commit or m_all.get("schema") != SCHEMA or m_all.get("core_commit") != core_commit:
            res["note"] = f"exported at another core commit or schema ({m_all.get('core_commit')}, {m_all.get('schema')})"
            return res
        mods = m_all.get("modules")
        if not isinstance(mods, dict):
            raise ValueError("no module table")
    except (OSError, ValueError, AttributeError) as e:
        res["note"] = f"unreadable manifest: {e}"[:300]
        return res
    build = os.path.join(tree, ".lake", "build")
    for f in files:
        m = f[:-len(".lean")]
        rec = mods.get(m) if eligible(m) else None
        if not isinstance(rec, dict) or not isinstance(rec.get("files"), dict):
            continue
        try:
            if rec.get("source_sha256") != _sha(os.path.join(tree, "submission", f)):
                continue        # changed: Lake builds it
            rels = [r for r in outputs(m) if r in rec["files"]]
            if f"lib/lean/{m}.olean" not in rels or f"lib/lean/{m}.trace" not in rels:
                continue
            if not all(_regular(os.path.join(src, r)) and _sha(os.path.join(src, r)) == rec["files"][r] for r in rels):
                continue
            for r in rels:
                _put(os.path.join(src, r), os.path.join(build, r))
            res["restored"].append(m)
        except OSError:
            for r in outputs(m):
                try:
                    os.remove(os.path.join(build, r))
                except OSError:
                    pass
    return res


def prune(tree, restored):
    """Remove the restored modules the build did not visit, so that the tree holds exactly
    Solution's import closure (Q7). Lake writes `M.olean.hash` for every module of the build,
    up to date or rebuilt, and restored modules come without one. Returns the removed modules."""
    build = os.path.join(tree, ".lake", "build")
    unused = [m for m in restored if not os.path.exists(os.path.join(build, "lib", "lean", f"{m}.olean.hash"))]
    for m in unused:
        for r in outputs(m):
            try:
                os.remove(os.path.join(build, r))
            except FileNotFoundError:
                pass
    return unused
