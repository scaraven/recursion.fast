#!/usr/bin/env python3
"""The harness's source rule (S6b-M3, S9D-M1; TRUSTED harness tool, interim until O-12).

  python3 -I scripts/source-rule.py [--net lexer|raw|both] DIR

Scans every `.lean` file under DIR (the submission-owned sources the harness copied into a fresh
tree) before anything is built, and rejects (exit 1, one line per finding) every use of what
elaboration-time code needs. A metaprogram run while a module is elaborated (`run_meta`, `#eval`,
…) leaves no declaration, so the gate cannot see it; the S7-M1 forgery and its raw variant
(`probes/s6b/gate/ForgeRaw.lean`: `persistentEnvExtensionsRef` + `unsafeCast` under Mathlib-only
imports) are such code. Two independent nets, both binding (`--net` selects one, for the tests):

1. **A lexer that follows Lean's** (`Lean.Parser.Basic`'s token functions), on code tokens only:
   `--` and nested `/- -/` comments; string literals with their escapes; raw strings only for `r`,
   then `#`s, then `"` (`r#check r` is the identifier `r` and the command `#check r`), closed by `"`
   and as many `#`s; character literals; `«…»` names; numbers as one token. Interpolation is a
   property of the syntax around a string, not of the lexer, so every string literal is read both
   ways, plainly and as `interpolatedStr` (`{…}` lexed recursively as code, with its own strings,
   comments and braces); the code parts are scanned, and a literal whose two readings end at
   different places (`s!"{ "}" }"`) is a finding. **Fail closed:** a comment, literal, name or
   interpolation still open at the end of the file is a finding, and so is a nesting of
   interpolations deeper than 4, and a file that is not UTF-8.
2. **A raw word scan** of the bytes, comments and strings included, which no lexer can be
   desynchronised from: the words below at ASCII word boundaries (never fewer boundaries than
   Lean's), wherever they stand. The cost is false positives in comments and strings, which the
   submitter rewords.

Rejected (the words and forms; a word is a whole word, so the Library's `run_mono` is not `run_…`):
  commands, tactics and terms that run code while elaborating: `run_meta`, `run_cmd`, `run_elab`,
    `run_tac`, Qq's `run_tacq`, Mathlib's `run_conv`, `by_elab`, Qq's `by_elabq`, `eval%`,
    `test_extern`, Mathlib's `compile_inductive%`/`compile_def%`, `elabToSyntax%`,
    `show_term_elab`, and every `#`-word except `#check`, `#print`, `#reduce`, `#guard_msgs` (so
    `#eval`, `#eval!`, `#exit`, `#guard`, `#time`, Plausible's `#test`, …; the literals `#[…]` and
    `#v[…]` and a `#` not followed by a letter are fine, Mathlib's `#s` is not: write `s.card`);
  definitions of elaborators, syntax and simprocs: `elab`, `elab_rules`, `macro`, `macro_rules`,
    `syntax`, `deprecated_syntax`, every `declare_…` (`declare_syntax_cat`, `declare_config_elab`,
    …), `simproc`, `dsimproc`, `simproc_decl`, `dsimproc_decl`, `simproc_pattern`, `cbv_simproc…`,
    `cbv_eval`, `def_eval_config_item`, `tactic_extension`, `leading_parser`, `trailing_parser`,
    `elab_stx_quot`, `grind_propagator`, `set_library_suggestions`, `idbg`, Mathlib's `sudo`, and
    the attributes `command_elab`, `term_elab`, `delab`, `app_unexpander`, `library_suggestions`,
    and after `[` or `,` also `tactic`, `init`, `export` and every `…_parser`, and every
    `builtin_…` (these leave declarations, which gate rules 3 and 7 also see);
  load-time code: `initialize`, `builtin_initialize`, every `register_…` command
    (`register_simp_attr`, `register_option`, … expand to `initialize`);
  `unsafe`, `partial`, and the names `unsafeCast`, `unsafeBaseIO`, `unsafeIO`, `unsafeEIO` (any
    word starting with `unsafe` or ending in `Unsafe`), `persistentEnvExtensionsRef`,
    `envExtensionsRef`;
  the attributes `implemented_by`, `extern`, `cpass`, `computed_field`, `csimp` (also gate rule 3);
  `set_option` of a compiler, elaborator or debug option (names starting with `compiler`, `debug`,
    `Elab`, `interpreter`, `bootstrap`, `trace.compiler`);
  `import Lean…`, `import Lake…` (also gate rule 6), `import Qq…`, `open Lean…` and `open Qq…`.
The word list was checked against the token table of the allowed import closure (Lean v4.34.1,
Mathlib and its packages, Clean; `scripts/TokenSweep.lean`, CI step 3: every keyword token is
either rejected here or listed as reviewed in `tests/source-rule/reviewed-tokens.txt`) and, for the
non-reserved and scoped keywords the table does not hold (`run_tac`, Qq's `by_elabq`), against the
packages' syntax declarations.
`tests/source-rule/check.sh` holds one fixture per rejected form, the S9 review's lexer bypasses
(each must be caught by each net alone), and a file of allowed forms. Notation, `deriving`,
`attribute [simp]`, `@[inline]`/`@[specialize]`/`@[elab_as_elim]`, tactics and `#check` are fine.
This raises the bar; it is not a proof that no elaboration-time code runs (O-12 is the sound fix).
"""
import bisect, os, re, sys

BANNED = {  # whole words (a longer identifier such as the Library's `run_mono` is not one of them)
    "run_meta", "run_cmd", "run_elab", "run_tac", "run_tacq", "run_conv", "by_elab", "by_elabq",
    "eval", "test_extern", "compile_inductive", "compile_def", "elabToSyntax", "show_term_elab",
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "deprecated_syntax",
    "initialize", "unsafe", "partial", "implemented_by", "extern", "cpass", "computed_field",
    "csimp", "persistentEnvExtensionsRef", "envExtensionsRef",
    "simproc", "dsimproc", "simproc_decl", "dsimproc_decl", "simproc_pattern", "cbv_simproc",
    "cbv_simproc_decl", "cbv_simproc_pattern", "cbv_eval", "def_eval_config_item",
    "command_elab", "term_elab", "delab", "app_unexpander", "tactic_extension",
    "leading_parser", "trailing_parser", "elab_stx_quot", "grind_propagator",
    "set_library_suggestions", "library_suggestions", "sudo", "idbg"}
BANNED_PREFIXES = ("register_", "builtin_", "declare_")   # every register_…/builtin_…/declare_… word
ATTRS = ("tactic", "init", "export")                  # banned only as attributes: `[` or `,` before
HASH_OK = {"#check", "#print", "#reduce", "#guard_msgs"}
OPTION_PREFIXES = ("compiler", "debug", "Elab", "interpreter", "bootstrap", "trace.compiler")
ID_START = re.compile(r"[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏\U0001d400-\U0001d7ff]")
ID_REST = re.compile(r"[A-Za-z0-9_'!?Ͱ-Ͽἀ-῿₀-ₜ℀-⅏\U0001d400-\U0001d7ff]")
CHAR_LIT = re.compile(r"'(\\(u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^\\'\n])'")
RAW_OPEN = re.compile(r'r(#*)"')
NUMBER = re.compile(r"0[xX][0-9a-fA-F_]*|0[bB][01_]*|0[oO][0-7_]*|[0-9][0-9_]*(\.[0-9]+)?([eE][+-]?[0-9]+)?")
MAX_INTERP_DEPTH = 4

# ---- net 2: the raw word scan --------------------------------------------------------------------
_B, _E, _EL = r"(?<![A-Za-z0-9_])", r"(?![A-Za-z0-9_])", r"(?![A-Za-z0-9_'!?])"
RAW = re.compile("|".join([
    _B + "(?:" + "|".join(BANNED_PREFIXES) + r"|unsafe)[A-Za-z0-9_]*",
    r"[A-Za-z0-9_]*Unsafe" + _E,
    _B + "(?:" + "|".join(sorted(BANNED - {"eval"}, key=len, reverse=True)) + ")" + _E,
    _B + r"eval\s*%",
    r"[\[,]\s*(?:local\s+|scoped\s+)?(?:" + "|".join(ATTRS) + r"|[A-Za-z0-9_]+_parser)" + _E,
    _B + r"set_option\s+(?:" + "|".join(re.escape(p) for p in OPTION_PREFIXES) + ")" + _EL,
    _B + r"import\s+(?:_root_\.)?(?:Lean|Lake|Qq)" + _EL,
    _B + r"open\s+(?:[A-Za-z0-9_.'!?«»]+\s+){0,20}?(?:_root_\.)?(?:Lean|Qq)" + _EL,
    r"#[A-Za-z_][A-Za-z0-9_'!?]*",
]))


def raw_findings(src, line_of):
    """Net 2: every match of `RAW`, comments and strings included."""
    out = []
    for m in RAW.finditer(src):
        w = m.group(0)
        if w.startswith("#") and (w in HASH_OK or (w == "#v" and src.startswith("[", m.end()))):
            continue
        out.append((line_of(m.start()), " ".join(w.split())))
    return out


# ---- net 1: the lexer ----------------------------------------------------------------------------
class TooComplex(Exception):
    """The lexer's work budget is exhausted (fail closed)."""


class Lexer:
    """Lean's lexical structure on `src`: code tokens (identifiers, `#`-words, symbols) with their
    offsets; what cannot be lexed safely goes to the problems (the fail-closed findings). Reading
    every string twice is memoised and bounded by a work budget (`TooComplex`)."""

    def __init__(self, src):
        self.src, self.n = src, len(src)
        self.budget = 64 * len(src) + 10 ** 6
        self.memo = {}

    def tick(self, k):
        self.budget -= k
        if self.budget < 0:
            raise TooComplex

    def lex(self, i, depth=0, stop=False):
        """(tokens, end, problems) from offset `i`. With `stop` (inside `{…}` of an interpolation):
        up to the unmatched `}`, whose offset is `end` (`None` if the file ends first)."""
        key = ("lex", i, depth, stop)
        if key in self.memo:
            return self.memo[key]
        src, n, toks, problems, braces, i0 = self.src, self.n, [], [], 0, i
        end = None if stop else n
        while i < n:
            c = src[i]
            if c.isspace():
                i += 1
            elif src.startswith("--", i):
                j = src.find("\n", i); i = n if j < 0 else j
            elif src.startswith("/-", i):
                i = self.block_comment(i, problems)
            elif c == '"':
                j, t, p = self.string(i, depth)
                toks += t; problems += p; i = j
            elif c == "r" and RAW_OPEN.match(src, i):           # r#…" only; r#check is r, #check
                i = self.raw_string(i, problems)
            elif c == "'" and CHAR_LIT.match(src, i):
                i = CHAR_LIT.match(src, i).end()
            elif c in "0123456789":
                i = NUMBER.match(src, i).end()
            elif c == "#" and i + 1 < n and ID_START.match(src[i + 1]):
                j = i + 1
                while j < n and ID_REST.match(src[j]): j += 1
                if src[i:j] == "#v" and j < n and src[j] == "[":   # the vector literal #v[…]
                    j += 1
                toks.append((src[i:j], i)); i = j
            elif ID_START.match(c) or c == "«":
                i = self.ident(i, toks, problems)
            else:
                if stop and c == "}" and braces == 0:
                    end = i
                    break
                braces += {"{": 1, "}": -1}.get(c, 0)
                toks.append((c, i)); i += 1
        self.tick(i - i0 + 1)
        self.memo[key] = (toks, end, problems)
        return self.memo[key]

    def block_comment(self, i, problems):
        depth, j = 1, i + 2
        while j < self.n and depth:
            if self.src.startswith("/-", j): depth += 1; j += 2
            elif self.src.startswith("-/", j): depth -= 1; j += 2
            else: j += 1
        if depth:
            problems.append((i, "comment still open at the end of the file"))
        return j

    def raw_string(self, i, problems):
        m = RAW_OPEN.match(self.src, i)
        end = self.src.find('"' + m.group(1), m.end())
        if end < 0:
            problems.append((i, "raw string still open at the end of the file"))
            return self.n
        return end + 1 + len(m.group(1))

    def ident(self, i, toks, problems):
        src, n, parts, j = self.src, self.n, [], i
        while True:
            if j < n and src[j] == "«":
                k = src.find("»", j)
                if k < 0:
                    problems.append((j, "«name» still open at the end of the file"))
                    toks.append((".".join(parts + [src[j + 1:]]), i))
                    return n
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
        toks.append((".".join(parts), i))
        return j

    def string(self, i, depth):
        """The string literal at `i`, read plainly and as an interpolated string: (offset after
        it, the code tokens of the second reading, problems)."""
        key = ("str", i, depth)
        if key in self.memo:
            return self.memo[key]
        src, n = self.src, self.n
        j = i + 1                                           # plain: up to the first unescaped "
        while j < n and src[j] != '"':
            j += 2 if src[j] == "\\" else 1
        self.tick(j - i)
        plain_end = j + 1 if j < n else None
        inner, sub, k, res = [], [], i + 1, None            # interpolated: {…} is code
        while k is not None and k < n and src[k] != '"':
            if src[k] == "\\":
                k += 2
            elif src[k] == "{":
                if depth >= MAX_INTERP_DEPTH:
                    res = (plain_end or n, [], [(i, f"interpolations nested deeper than {MAX_INTERP_DEPTH}")])
                    break
                t, k, p = self.lex(k + 1, depth + 1, stop=True)
                inner += t; sub += p
                if k is not None:
                    k += 1
            else:
                k += 1
        if res is None:
            interp_end = k + 1 if k is not None and k < n else None
            if plain_end is None:
                res = (n, [], [(i, "string literal still open at the end of the file")])
            elif interp_end != plain_end:
                res = (plain_end, [], [(i, "string literal whose end depends on whether it is "
                                           "interpolated (a string, comment or unbalanced brace inside `{…}`)")])
            else:
                res = (plain_end, inner, sub)
        self.memo[key] = res
        return res


def lexer_findings(src, line_of):
    """Net 1: the lexer's problems, and the banned forms among the code tokens."""
    try:
        toks, _, problems = Lexer(src).lex(0)
    except TooComplex:
        return [(1, "too complex to lex within the work budget")]
    toks = sorted(toks, key=lambda t: t[1])
    bad = [(line_of(o), what) for o, what in problems]
    for k, (t, o) in enumerate(toks):
        ln = line_of(o)
        nxt = toks[k + 1][0] if k + 1 < len(toks) else ""
        comps = t.split(".")
        if t == "eval":                                     # `eval%`; `eval` alone is a name
            if nxt == "%":
                bad.append((ln, "eval%"))
        elif t in BANNED or t.startswith(BANNED_PREFIXES) or \
                any(c in ("persistentEnvExtensionsRef", "envExtensionsRef") for c in comps):
            bad.append((ln, t))
        elif t.startswith("#") and len(t) > 1 and t not in HASH_OK and t != "#v[":
            bad.append((ln, t))
        elif any(c.startswith("unsafe") or c.endswith("Unsafe") for c in comps if c):
            bad.append((ln, t))
        elif t in ("[", ","):
            j = k + 1
            if nxt in ("local", "scoped"): j += 1
            if j < len(toks) and (toks[j][0] in ATTRS or toks[j][0].endswith("_parser")):
                bad.append((ln, f"attribute {toks[j][0]}"))
        elif t == "set_option" and any(nxt == p or nxt.startswith(p + ".") for p in OPTION_PREFIXES):
            bad.append((ln, f"set_option {nxt}"))
        elif t == "import" and (nxt.removeprefix("_root_.").split(".")[0] in ("Lean", "Lake", "Qq")):
            bad.append((ln, f"import {nxt}"))
        elif t == "open":
            j = k + 1
            while j < len(toks) and line_of(toks[j][1]) == ln and toks[j][0] not in ("in", "hiding", "renaming", "("):
                if toks[j][0].removeprefix("_root_.").split(".")[0] in ("Lean", "Qq"):
                    bad.append((ln, f"open {toks[j][0]}"))
                j += 1
    return bad


def findings(src, net="both"):
    """(line, what) pairs: net 1's, then net 2's on the lines net 1 did not report."""
    nl = [i for i, c in enumerate(src) if c == "\n"]
    line_of = lambda off: bisect.bisect_left(nl, off) + 1
    lex = lexer_findings(src, line_of) if net in ("lexer", "both") else []
    raw = raw_findings(src, line_of) if net in ("raw", "both") else []
    seen = {ln for ln, _ in lex}
    return sorted(lex) + sorted((ln, f"{w} (raw scan)") for ln, w in raw if ln not in seen)


def main():
    args, net = sys.argv[1:], "both"
    if len(args) == 3 and args[0] == "--net" and args[1] in ("lexer", "raw", "both"):
        net, args = args[1], args[2:]
    if len(args) != 1 or not os.path.isdir(args[0]):
        raise SystemExit("usage: source-rule.py [--net lexer|raw|both] DIR")
    root, total, nfiles = args[0], 0, 0
    for d, _, fs in sorted(os.walk(root)):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            nfiles += 1
            try:
                with open(p, encoding="utf-8", errors="strict") as fh:
                    src = fh.read()
                found = findings(src, net)
            except (OSError, UnicodeDecodeError) as e:         # fail closed
                found = [(1, f"unreadable ({e.__class__.__name__})")]
            except RecursionError:
                found = [(1, "too deeply nested to scan")]
            for ln, what in found:
                print(f"source-rule: {os.path.relpath(p, root)}:{ln}: {what}")
                total += 1
    print(f"source-rule: {nfiles} files, {total} finding(s)")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
