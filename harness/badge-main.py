#!/usr/bin/env python3
"""Render the badge executable's main module from harness/lean/Main.lean.in (Stage 6b).

  python3 -I harness/badge-main.py OUT.lean MODULE SUBMISSION verify|index

MODULE is the submission's Lean module (e.g. the solution module of the gate tree), SUBMISSION the
constant (e.g. RecursionFast.Challenge.submission). Both must be dotted Lean identifiers; nothing
else is substituted. The entry point is RecursionFastHarness.verifyMain or .indexMain."""
import os, re, sys

if len(sys.argv) != 5 or sys.argv[4] not in ("verify", "index"):
    raise SystemExit(__doc__)
out, module, submission, exe = sys.argv[1:]
ident = r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*"
for what, v in (("module", module), ("submission", submission)):
    if not re.fullmatch(ident, v):
        raise SystemExit(f"badge-main: {what} {v!r} is not a dotted Lean identifier")
tmpl = open(os.path.join(os.path.dirname(os.path.realpath(__file__)), "lean", "Main.lean.in")).read()
text = (tmpl.replace("{{module}}", module).replace("{{submission}}", submission)
        .replace("{{exe}}", exe).replace("{{entry}}", exe + "Main"))
assert "{{" not in text
open(out, "w").write(text)
