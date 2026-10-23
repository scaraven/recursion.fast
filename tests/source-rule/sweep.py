#!/usr/bin/env python3
"""The keyword sweep of the source rule (S9D-M1 fix pass).

  python3 -I tests/source-rule/sweep.py SOURCE_RULE.py TOKENS.txt REVIEWED.txt

TOKENS.txt is `scripts/TokenSweep.lean`'s output (the token table of the allowed import closure).
Every keyword-like token (a word, a `#`-word, a word ending in `%`) must be rejected by
SOURCE_RULE.py (a file holding the token alone has a finding) or be listed in REVIEWED.txt (one
token per line, `--` comments allowed). Exit 1, naming the tokens, if one is neither; reviewed
tokens no longer in the table are reported, not failed."""
import importlib.util, re, sys

def main():
    rule, tokens, reviewed = sys.argv[1:4]
    spec = importlib.util.spec_from_file_location("source_rule", rule)
    sr = importlib.util.module_from_spec(spec); spec.loader.exec_module(sr)
    words = sorted({t for t in open(tokens, encoding="utf-8").read().split("\n")
                    if re.fullmatch(r"#?[A-Za-z_][A-Za-z0-9_'!?.]*%?", t)})
    ok = {l.split("--")[0].strip() for l in open(reviewed, encoding="utf-8")} - {""}
    rejected = [w for w in words if sr.findings(w + "\n")]
    unreviewed = [w for w in words if w not in rejected and w not in ok]
    gone = sorted(ok - set(words))
    print(f"sweep: {len(words)} keyword tokens: {len(rejected)} rejected by the source rule, "
          f"{len(words) - len(rejected) - len(unreviewed)} reviewed, {len(unreviewed)} unreviewed")
    if gone:
        print(f"sweep: reviewed but no longer in the table: {' '.join(gone)}")
    if unreviewed:
        print(f"sweep: UNREVIEWED keywords (ban them in scripts/source-rule.py, or review and list "
              f"them in {reviewed}): {' '.join(unreviewed)}")
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
