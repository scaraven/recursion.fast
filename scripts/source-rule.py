#!/usr/bin/env python3
"""The harness's source rule (S6b-M3 fix pass; TRUSTED harness tool, interim until O-12).

  python3 -I scripts/source-rule.py DIR

Scans every `.lean` file under DIR (the submission-owned sources the harness copied into a fresh
tree) before anything is built, and rejects (exit 1, one line per finding) every use of what
elaboration-time code needs. A metaprogram run while a module is elaborated (`run_meta`, `#eval`,
…) leaves no declaration, so the gate cannot see it; the S7-M1 forgery and its raw variant
(`probes/s6b/gate/ForgeRaw.lean`: `persistentEnvExtensionsRef` + `unsafeCast` under Mathlib-only
imports) are such code. The rule works on tokens, not substrings: comments (nested `/- -/`, `--`),
string and character literals are skipped, except the `{…}` code parts of interpolated strings
(`s!"…"`), and `«…»` names are unescaped.

Rejected:
  commands, tactics and terms that run code while elaborating: every word starting `run_`
    (`run_meta`, `run_cmd`, `run_elab`, `run_tac`, Qq's `run_tacq`, Mathlib's `run_conv`),
    `by_elab`, Qq's `by_elabq`, `eval%`, and every `#`-word except `#check`, `#print`, `#reduce`,
    `#guard_msgs` (so `#eval`, `#eval!`, `#exit`, `#guard`, Plausible's `#test`, …; the literals
    `#[…]` and `#v[…]` and a `#` not followed by a letter are fine, Mathlib's `#s` is not: write
    `s.card`);
  definitions of elaborators, syntax and simprocs: `elab`, `elab_rules`, `macro`, `macro_rules`,
    `syntax`, `declare_syntax_cat`, `simproc`, `dsimproc`, `simproc_decl`, `dsimproc_decl` (these
    leave declarations, which gate rule 7 also rejects);
  load-time code: `initialize`, `builtin_initialize`, every `register_…` command
    (`register_simp_attr`, `register_option`, … expand to `initialize`);
  `unsafe`, `partial`, and the names `unsafeCast`, `unsafeBaseIO`, `unsafeIO`, `unsafeEIO` (any
    name component starting with `unsafe` or ending in `Unsafe`), `persistentEnvExtensionsRef`,
    `envExtensionsRef`;
  the attributes `implemented_by`, `extern`, `cpass`, `computed_field` (also gate rule 3);
  `set_option` of a compiler, elaborator or debug option (names starting with `compiler`, `debug`,
    `Elab`, `interpreter`, `bootstrap`, `trace.compiler`);
  `import Lean…`, `import Lake…` (also gate rule 6), `import Qq…`, `open Lean…` and `open Qq…`.
The word list was checked against the keywords of Lean v4.34.1 and of the packages in Mathlib's
closure (Batteries, Qq, Aesop, Plausible, ProofWidgets) that run code without leaving a declaration
(`tests/source-rule/`: one fixture per rejected form, one with the allowed forms).
Notation, `deriving`, `attribute [simp]`, `@[inline]`/`@[specialize]`, tactics and `#check` are fine.
This raises the bar; it is not a proof that no elaboration-time code runs (O-12 is the sound fix).
"""
import os, re, sys

BANNED = {"run_meta", "run_cmd", "run_elab", "run_tac", "by_elab", "elab", "elab_rules", "macro",
          "macro_rules", "syntax", "declare_syntax_cat", "initialize", "builtin_initialize",
          "unsafe", "partial", "implemented_by", "extern", "cpass", "computed_field",
          "persistentEnvExtensionsRef", "envExtensionsRef", "by_elabq", "simproc", "dsimproc",
          "simproc_decl", "dsimproc_decl"}
HASH_OK = {"#check", "#print", "#reduce", "#guard_msgs"}
OPTION_PREFIXES = ("compiler", "debug", "Elab", "interpreter", "bootstrap", "trace.compiler")
ID_START = re.compile(r"[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏\U0001d400-\U0001d7ff]")
ID_REST = re.compile(r"[A-Za-z0-9_'!?Ͱ-Ͽἀ-῿₀-ₜ℀-⅏\U0001d400-\U0001d7ff]")
CHAR_LIT = re.compile(r"'(\\(u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^\\'\n])'")


def tokens(src, line=1):
    """(token, line) pairs of Lean source `src`: identifiers (dotted, `«»` unescaped), `#name`,
    `%`, and single symbol characters; comments and literals skipped (interpolations scanned)."""
    out, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1; i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j
        elif src.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/-", i): depth += 1; i += 2
                elif src.startswith("-/", i): depth -= 1; i += 2
                else:
                    line += src[i] == "\n"; i += 1
        elif c == '"' or (c == "r" and i + 1 < n and src[i + 1] in '"#' and (i == 0 or not ID_REST.match(src[i - 1]))):
            interp = c == '"' and i > 0 and src[i - 1] == "!"
            if c == "r":                                        # raw string r#"…"#
                j = i + 1
                while j < n and src[j] == "#": j += 1
                hashes = j - i - 1
                end = src.find('"' + "#" * hashes, j + 1)
                end = n if end < 0 else end + 1 + hashes
                line += src.count("\n", i, end); i = end
                continue
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\": i += 2; continue
                if interp and src[i] == "{":                    # code inside s!"…{code}…"
                    depth, j = 1, i + 1
                    while j < n and depth:
                        depth += {"{": 1, "}": -1}.get(src[j], 0); j += 1
                    out += tokens(src[i + 1:j - 1], line)
                    line += src.count("\n", i, j); i = j; continue
                line += src[i] == "\n"; i += 1
            i += 1
        elif c == "'" and CHAR_LIT.match(src, i) and (i == 0 or not ID_REST.match(src[i - 1])):
            i = CHAR_LIT.match(src, i).end()
        elif c == "#" and i + 1 < n and ID_START.match(src[i + 1]):
            j = i + 1
            while j < n and ID_REST.match(src[j]): j += 1
            if src[i:j] == "#v" and j < n and src[j] == "[":   # the vector literal #v[…]
                j += 1
            out.append((src[i:j], line)); i = j
        elif ID_START.match(c) or c == "«":
            parts, j = [], i
            while True:
                if j < n and src[j] == "«":
                    k = src.find("»", j); k = n if k < 0 else k
                    parts.append(src[j + 1:k]); j = k + 1
                elif j < n and ID_START.match(src[j]):
                    k = j + 1
                    while k < n and ID_REST.match(src[k]): k += 1
                    parts.append(src[j:k]); j = k
                else:
                    break
                if j + 1 < n and src[j] == "." and (ID_START.match(src[j + 1]) or src[j + 1] == "«"):
                    j += 1
                else:
                    break
            out.append((".".join(parts), line)); i = j
        elif c.isspace():
            i += 1
        else:
            out.append((c, line)); i += 1
    return out


def findings(src):
    toks, bad = tokens(src), []
    for k, (t, ln) in enumerate(toks):
        nxt = toks[k + 1][0] if k + 1 < len(toks) else ""
        comps = t.split(".")
        if t in BANNED or t.startswith("run_") or \
                any(c in ("persistentEnvExtensionsRef", "envExtensionsRef") for c in comps):
            bad.append((ln, t))
        elif t.startswith("#") and len(t) > 1 and t not in HASH_OK and t != "#v[":
            bad.append((ln, t))
        elif t == "eval" and nxt == "%":
            bad.append((ln, "eval%"))
        elif t.startswith("register_"):
            bad.append((ln, t))
        elif any(c.startswith("unsafe") or c.endswith("Unsafe") for c in comps if c):
            bad.append((ln, t))
        elif t == "set_option" and any(nxt == p or nxt.startswith(p + ".") for p in OPTION_PREFIXES):
            bad.append((ln, f"set_option {nxt}"))
        elif t == "import" and (nxt.removeprefix("_root_.").split(".")[0] in ("Lean", "Lake", "Qq")):
            bad.append((ln, f"import {nxt}"))
        elif t == "open":
            j = k + 1
            while j < len(toks) and toks[j][1] == ln and toks[j][0] not in ("in", "hiding", "renaming", "("):
                if toks[j][0].removeprefix("_root_.").split(".")[0] in ("Lean", "Qq"):
                    bad.append((ln, f"open {toks[j][0]}"))
                j += 1
    return bad


def main():
    if len(sys.argv) != 2 or not os.path.isdir(sys.argv[1]):
        raise SystemExit("usage: source-rule.py DIR")
    root, total, nfiles = sys.argv[1], 0, 0
    for d, _, fs in sorted(os.walk(root)):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            nfiles += 1
            with open(p, encoding="utf-8", errors="strict") as fh:
                for ln, what in findings(fh.read()):
                    print(f"source-rule: {os.path.relpath(p, root)}:{ln}: {what}")
                    total += 1
    print(f"source-rule: {nfiles} files, {total} finding(s)")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
