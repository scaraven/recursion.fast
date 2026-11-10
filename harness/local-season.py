#!/usr/bin/env python3
"""Print a copy of the season file for a local run at the season's shape (untrusted helper).

  python3 -I harness/local-season.py [SEASON] > season-local.toml

The copy is `harness/season.toml` (or SEASON) with two lines changed, as `harness/smoke.toml`
has them, and nothing else: every shape and cap stays the season's.

- `[machine] fingerprint = "any"`: your machine is not the evaluation machine, whose fingerprint
  check would otherwise stop the run as an organiser ERROR before the prover is built;
- `[calibration] ref_provisional = true`: `c_P` against the season's `ref_ns` is recorded, not
  enforced (your machine's `calib` time is not the season's).

The season name gains `-local`. A local run is never attested and is not a result.
"""
import os
import re
import sys
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
LOCAL = {"fingerprint": '"any"', "ref_provisional": "true"}


def local_season(text):
    """The local copy of a season file's text; each changed key must occur exactly once."""
    for key, value in LOCAL.items():
        text, n = re.subn(rf"(?m)^{key} *=[^\n]*$", f"{key} = {value}   # local run (harness/local-season.py)", text)
        if n != 1:
            raise SystemExit(f"local-season: `{key} =` occurs {n} times at the start of a line, expected 1")
    text, n = re.subn(r'(?m)^name = "([^"\n]*)"', r'name = "\1-local"', text, count=1)
    if n != 1:
        raise SystemExit("local-season: no `name =` line")
    t = tomllib.loads(text)
    for table, key, want in (("machine", "fingerprint", "any"), ("calibration", "ref_provisional", True)):
        if t.get(table, {}).get(key) != want:
            raise SystemExit(f"local-season: [{table}] {key} is not {want!r} in the copy; "
                             "the season file's layout changed")
    return ("# A local copy of the season file (harness/local-season.py): not the season, never attested.\n"
            + text)


if __name__ == "__main__":
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "season.toml")
    sys.stdout.write(local_season(open(src, encoding="utf-8").read()))
