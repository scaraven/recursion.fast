#!/usr/bin/env python3
"""Render a Challenge/*.lean.in stub into a challenge file (v0.3, A4-F2/F5).

  scripts/render-challenge.py STUB.lean.in claim.json OUT.lean

Placeholders (anything else between double braces is an error):
  {{nat:KEY}}    a natural number < 2^64                 claim[KEY]: JSON integer (not bool)
  {{rat:KEY}}    a non-negative rational, as (a / b : Q)  claim[KEY]: string "a" or "a/b" (b > 0)
  {{image:KEY}}  on a line of its own: the definitions of an `Image` named KEY, rendered from
                 raw files                                claim[KEY]: {"code": path, "data": path,
                                                          "harts": bool}; `.code` = little-endian
                                                          32-bit words, `.data` = little-endian
                                                          64-bit words (plain relative paths to
                                                          regular files inside the claim file's
                                                          directory: no absolute path, `..` or
                                                          symlink, A6-R1); code + data <= 2^20 bytes
Strict schema: the claim's key set must equal the stub's placeholder key set (no missing, no
extra keys), every value must have exactly the placeholder's type. The image bytes are read from
the submitted files by the harness and rendered as challenge data: nothing is evaluated from a
solution (the emulator and the scorer use the same files and the rendered numbers).
"""
import json, os, re, struct, sys

MAX_RAT_DIGITS = 5000
CHUNK = 256
PH = re.compile(r"\{\{(nat|rat|image):([A-Za-z0-9_.]+)\}\}")

def fail(msg):
    raise SystemExit(f"render-challenge: {msg}")

def nat(k, v):
    if type(v) is not int or not (0 <= v < 2 ** 64):
        fail(f"{k}: expected a JSON integer in [0, 2^64), got {v!r}")
    return str(v)

def rat(k, v):
    if type(v) is not str or not re.fullmatch(r"[0-9]+(/[1-9][0-9]*)?", v) or len(v) > 2 * MAX_RAT_DIGITS:
        fail(f"{k}: expected a string 'a' or 'a/b' of decimal digits, got {v!r}")
    a, _, b = v.partition("/")
    return f"(({a} : ℚ) / {b or 1})"

def confined(k, rel, base):
    """A6-R1: the claim names files only inside its own directory `base`: a relative path, no `..`
    or empty component, no symbolic link on the way, a regular file. (Better still, the harness
    supplies the image paths itself.)"""
    parts = rel.split("/")
    if os.path.isabs(rel) or "\\" in rel or any(p in ("", ".", "..") for p in parts):
        fail(f"{k}: image path {rel!r} must be a plain relative path inside the claim's directory")
    p = base
    for part in parts:
        p = os.path.join(p, part)
        if os.path.islink(p):
            fail(f"{k}: image path {rel!r} goes through a symbolic link")
    if os.path.commonpath([os.path.realpath(p), base]) != base or not os.path.isfile(p):
        fail(f"{k}: image path {rel!r} is not a regular file inside the claim's directory")
    return p

def words(path, width):
    data = open(path, "rb").read()
    if len(data) % width:
        fail(f"{path}: length {len(data)} is not a multiple of {width}")
    return list(struct.unpack(f"<{len(data) // width}{'I' if width == 4 else 'Q'}", data))

def lean_list(name, ty, ws, bits):
    """Packed encoding: chunks of CHUNK words, each one natural literal (little-endian `bits`-bit
    words), decoded by the contract's `unpack`. Elaboration is ~13 s for a 1 MiB image (a list
    literal of 2^18 `BitVec` literals takes > 250 s and 7 GB). The chunk list is a separate
    definition so that a solver checks the chunk lengths once (`decide +kernel`, ~28 s at 1 MiB)
    and then looks up a word inside one chunk (`Library/Image.lean`, `getElem?_chunks'`) instead
    of walking the prefix (~80 s and 9 GB per lookup at 1 MiB)."""
    out, parts = [], []
    for i in range(0, len(ws), CHUNK):
        part = ws[i:i + CHUNK]
        n = sum(w << (bits * j) for j, w in enumerate(part))
        cn = f"{name}_{i // CHUNK}"
        parts.append(f"unpack {bits} {len(part)} {cn}")
        out.append(f"def {cn} : ℕ := 0x{n:x}")
    out.append(f"/-- Chunks of the submitted file ({len(ws)} words), {CHUNK} words each but the last. -/\n"
               f"def {name}_chunks : List (List ℕ) := [{', '.join(parts)}]")
    out.append(f"/-- Rendered from the submitted file (lookups: `Library/Image.lean`, `getElem?_chunks'`). -/\n"
               f"def {name} : List ({ty}) := {name}_chunks.flatten.map (BitVec.ofNat {bits})")
    return out

def image(k, v, base):
    if type(v) is not dict or set(v) != {"code", "data", "harts"}:
        fail(f"{k}: expected an object with exactly the keys code, data, harts, got {v!r}")
    if type(v["harts"]) is not bool or type(v["code"]) is not str or type(v["data"]) is not str:
        fail(f"{k}: code/data must be paths, harts a boolean")
    code = words(confined(k, v["code"], base), 4)
    data = words(confined(k, v["data"], base), 8)
    if 4 * len(code) + 8 * len(data) > 2 ** 20:
        fail(f"{k}: image of {4 * len(code) + 8 * len(data)} bytes exceeds 2^20")
    name = k.replace(".", "_")
    out = lean_list(f"{name}_code", "BitVec 32", code, 32) + lean_list(f"{name}_data", "Word", data, 64)
    out.append(f"/-- The submitted image (rendered challenge data). -/\n"
               f"def {name} : Image := {{ code := {name}_code, data := {name}_data, "
               f"harts := {'true' if v['harts'] else 'false'} }}")
    return "\n".join(out)

def main():
    stub, claim_path, out = sys.argv[1:4]
    sys.set_int_max_str_digits(0)
    text = open(stub).read()
    vals = json.load(open(claim_path), parse_float=lambda s: fail(f"float {s} not allowed"))
    if type(vals) is not dict:
        fail("claim must be a JSON object")
    found = {}
    for kind, key in PH.findall(text):
        if found.setdefault(key, kind) != kind:
            fail(f"placeholder {key} used with two types")
    if set(vals) != set(found):
        fail(f"key mismatch: missing {sorted(set(found) - set(vals))}, extra {sorted(set(vals) - set(found))}")
    base = os.path.realpath(os.path.dirname(os.path.abspath(claim_path)))
    def sub(m):
        kind, key = m.groups()
        if kind == "nat": return nat(key, vals[key])
        if kind == "rat": return rat(key, vals[key])
        line_start = m.string.rfind("\n", 0, m.start()) + 1
        if m.string[line_start:m.start()].strip():
            fail(f"image placeholder {key} must be on a line of its own")
        return image(key, vals[key], base)
    rendered = PH.sub(sub, text)
    if "{{" in rendered:
        fail("unrendered or malformed placeholder left")
    open(out, "w").write(rendered)

if __name__ == "__main__":
    main()
