#!/usr/bin/env python3
"""Render the badge executable's main module from harness/lean/Main.lean.in (Stage 6b).

  python3 -I harness/badge-main.py OUT.lean MODULE SUBMISSION verify|index [--certified-c C.lean]

MODULE is the submission's Lean module (e.g. the solution module of the gate tree), SUBMISSION the
constant (e.g. RecursionFast.Challenge.submission). Both must be dotted Lean identifiers; nothing
else is substituted. The entry point is RecursionFastHarness.verifyMain or .indexMain.

`--certified-c C.lean` (index only; S9D-m4): C.lean holds the definitions of a `Layout K` named `C`
rendered by scripts/render-challenge.py from the stub line `{{layout:C}}` and the claim's layout
file (the same rendering as the challenge's certified `C`; scripts/harness.sh,
harness/badge-build.sh). They are inlined into the main module (namespace
`RecursionFastHarness.Certified`), and `index --certified-C VKC_OUT` indexes that `C`."""
import os, re, sys

args = sys.argv[1:]
cert = None
if len(args) == 6 and args[4] == "--certified-c":
    cert, args = args[5], args[:4]
if len(args) != 4 or args[3] not in ("verify", "index") or (cert and args[3] != "index"):
    raise SystemExit(__doc__)
out, module, submission, exe = args
ident = r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*"
for what, v in (("module", module), ("submission", submission)):
    if not re.fullmatch(ident, v):
        raise SystemExit(f"badge-main: {what} {v!r} is not a dotted Lean identifier")
certified, entry_args = "", ""
if exe == "index":
    entry_args = "none "
if cert:
    body = open(cert, encoding="utf-8").read()
    if not re.search(r"(?m)^def C : Layout K :=$", body) or "{{" in body or re.search(r"(?m)^(import|namespace|end|open)\b", body):
        raise SystemExit(f"badge-main: {cert} is not the rendering of `{{{{layout:C}}}}`")
    certified = ("/-! The certified recursion layout `C`, rendered from the claim (S9D-m4). -/\n"
                 "namespace RecursionFastHarness.Certified\n\n" + body.rstrip() + "\n\nend RecursionFastHarness.Certified\n")
    entry_args = "(some RecursionFastHarness.Certified.C) "
tmpl = open(os.path.join(os.path.dirname(os.path.realpath(__file__)), "lean", "Main.lean.in")).read()
text = (tmpl.replace("{{module}}", module).replace("{{submission}}", submission)
        .replace("{{exe}}", exe).replace("{{entry}}", exe + "Main").replace("{{entry_args}}", entry_args))
text = text.replace("{{certified}}", certified)          # last: the rendered layout is data
assert "{{" not in text.replace(certified, "") if certified else "{{" not in text
open(out, "w").write(text)
