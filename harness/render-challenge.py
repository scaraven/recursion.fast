#!/usr/bin/env python3
"""Render the v4 challenge stub with an entry's claim (TRUSTED harness tool; v3's renderer, the
interim `scripts/render-challenge.py` of `v3/s2-interim-harness`, cut to the kinds v4's `Declared`
needs).

  python3 -I harness/render-challenge.py harness/challenge/Challenge.lean.in claim.json OUT.lean

  {{nat:KEY}}    a natural number < 2^64        claim[KEY]: a JSON integer (not a bool)
  {{rat:KEY}}    a non-negative rational, as     claim[KEY]: the string "a" or "a/b" (b > 0)
                 an `ℝ≥0` (`((a : ℝ≥0) / b)`)

Strict schema: the claim's key set equals the stub's placeholder key set; every value has exactly
the placeholder's type; a JSON float, NaN/Infinity or a duplicate key is an error.
"""
import json
import re
import sys

MAX_RAT_DIGITS = 5000
PH = re.compile(r"\{\{(nat|rat):([A-Za-z0-9_.]+)\}\}")
U64 = 2 ** 64


def fail(msg):
    msg = str(msg)
    raise SystemExit(f"render-challenge: {msg if len(msg) <= 300 else msg[:300] + ' ...'}")


def nat(k, v):
    if type(v) is not int or not (0 <= v < U64):
        fail(f"{k}: expected a JSON integer in [0, 2^64), got {v!r}")
    return str(v)


def rat(k, v):
    if type(v) is not str or not re.fullmatch(r"[0-9]+(/[1-9][0-9]*)?", v) or len(v) > 2 * MAX_RAT_DIGITS:
        fail(f"{k}: expected a string 'a' or 'a/b' of decimal digits, got {v!r}")
    a, _, b = v.partition("/")
    return f"(({a} : ℝ≥0) / {b or 1})"


def strict_json(path, what):
    def pairs(ps):
        d = {}
        for key, val in ps:
            if key in d:
                fail(f"{what}: duplicate key {key!r}")
            d[key] = val
        return d

    def bad_const(s):
        fail(f"{what}: {s} not allowed")
    try:
        with open(path) as f:
            return json.load(f, object_pairs_hook=pairs, parse_constant=bad_const,
                             parse_float=lambda s: fail(f"{what}: float {s} not allowed"))
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        fail(f"{what}: not JSON ({e})")


def render(stub_text, vals):
    if type(vals) is not dict:
        fail("claim must be a JSON object")
    found = {}
    for kind, key in PH.findall(stub_text):
        if found.setdefault(key, kind) != kind:
            fail(f"placeholder {key} used with two types")
    if set(vals) != set(found):
        fail(f"key mismatch: missing {sorted(set(found) - set(vals))}, extra {sorted(set(vals) - set(found))}")
    out = PH.sub(lambda m: (nat if m.group(1) == "nat" else rat)(m.group(2), vals[m.group(2)]), stub_text)
    if "{{" in out:
        fail("unrendered or malformed placeholder left")
    return out


def main():
    if len(sys.argv) != 4:
        fail("usage: render-challenge.py STUB.lean.in claim.json OUT.lean")
    sys.set_int_max_str_digits(0)
    out = render(open(sys.argv[1]).read(), strict_json(sys.argv[2], "claim"))
    with open(sys.argv[3], "w") as f:
        f.write(out)


if __name__ == "__main__":
    main()
