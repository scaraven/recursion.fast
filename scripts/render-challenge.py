#!/usr/bin/env python3
"""Render a Challenge/*.lean.in stub into a challenge file (v0.3, A4-F2/F5; v2 placeholders S6b).

  python3 -I scripts/render-challenge.py STUB.lean.in claim.json OUT.lean

Placeholders (anything else between double braces is an error):
  {{nat:KEY}}     a natural number < 2^64                  claim[KEY]: JSON integer (not bool)
  {{rat:KEY}}     a non-negative rational, as (a / b : Q)   claim[KEY]: string "a" or "a/b" (b > 0)
  {{hash:KEY}}    a `HashId` of the `Cfg` menu              claim[KEY]: one of "blake2s"
  {{digest:KEY}}  a 32-byte `Digest` (`List UInt8`)         claim[KEY]: 64 lowercase hex digits
  {{image:KEY}}   on a line of its own: the definitions of an `Image` named KEY, rendered from raw
                  files                                     claim[KEY]: {"code": path, "data": path};
                                                            `.code` = little-endian 32-bit words,
                                                            `.data` = little-endian 64-bit words;
                                                            code + data <= 2^20 bytes (`imageCap`)
  {{layout:KEY}}  on a line of its own: the definitions of a `Layout K` named KEY (one `Chip K` per
                  chip, `KEY_chipI`), rendered by harness/render-layout.py's emitter from a layout
                  JSON (schema recursion.fast/layout/1, harness/README.md)
                                                            claim[KEY]: path of the layout JSON
Paths are plain relative paths to regular files inside the claim file's directory (no absolute
path, `..` or symbolic link, A6-R1).

Strict schema: the claim's key set must equal the stub's placeholder key set (no missing, no extra
keys); every value must have exactly the placeholder's type; a JSON float, NaN/Infinity or a
duplicate object key anywhere (claim or layout) is an error. A layout is checked so that its Lean
literal is exactly the JSON's layout: every number a JSON integer in [0, 2^64), every K element 16
lowercase hex digits, `|M| = t`, `|S| = |c| = q`, every matrix entry `(row, col, v)` with
`row < cons` and `col < 2·cols + 3`, every `S` entry `< t` (a `Fin` literal out of range would
silently wrap), only the documented keys; its informational strings never reach the output (the
emitter sees a copy without them). If the claim also has nat keys `KEY.chips` / `KEY.entries` they
must equal the layout's chip count and total number of matrix entries (`CertificateR.size`).

The image bytes and the layout are read from the submitted files by the harness and rendered as
challenge data: nothing is evaluated from a solution (the badge path's indexer reads the same
layout file, harness/README.md).
"""
import importlib.util, json, os, re, struct, sys

MAX_RAT_DIGITS = 5000
CHUNK = 256
PH = re.compile(r"\{\{(nat|rat|hash|digest|image|layout):([A-Za-z0-9_.]+)\}\}")
HASHES = {"blake2s": ".blake2s"}            # Contract/Compile.lean `HashId` (grows with Lean specs)
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
    return f"(({a} : ℚ) / {b or 1})"

def hashid(k, v):
    if type(v) is not str or v not in HASHES:
        fail(f"{k}: expected a hash of the menu {sorted(HASHES)}, got {v!r}")
    return HASHES[v]

def digest(k, v):
    if type(v) is not str or not re.fullmatch(r"[0-9a-f]{64}", v):
        fail(f"{k}: expected a 32-byte digest as 64 lowercase hex digits, got {v!r}")
    return "[" + ", ".join(f"0x{v[i:i + 2]}" for i in range(0, 64, 2)) + "]"

def confined(k, rel, base):
    """A6-R1: the claim names files only inside its own directory `base`: a relative path, no `..`
    or empty component, no symbolic link on the way, a regular file. (Better still, the harness
    supplies the paths itself.)"""
    if type(rel) is not str:
        fail(f"{k}: expected a path string, got {rel!r}")
    parts = rel.split("/")
    if os.path.isabs(rel) or "\\" in rel or any(p in ("", ".", "..") for p in parts):
        fail(f"{k}: path {rel!r} must be a plain relative path inside the claim's directory")
    p = base
    for part in parts:
        p = os.path.join(p, part)
        if os.path.islink(p):
            fail(f"{k}: path {rel!r} goes through a symbolic link")
    if os.path.commonpath([os.path.realpath(p), base]) != base or not os.path.isfile(p):
        fail(f"{k}: path {rel!r} is not a regular file inside the claim's directory")
    return p

def strict_json(path, what):
    """JSON with no float, no NaN/Infinity and no duplicate key (two readers could disagree)."""
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

def words(path, width):
    data = open(path, "rb").read()
    if len(data) % width:
        fail(f"{path}: length {len(data)} is not a multiple of {width}")
    return list(struct.unpack(f"<{len(data) // width}{'I' if width == 4 else 'Q'}", data))

def lean_list(name, ty, ws, bits):
    """Packed encoding: chunks of CHUNK words, each one natural literal (little-endian `bits`-bit
    words), decoded by the contract's `unpack`. Elaboration is ~13 s for a 1 MiB image (a list
    literal of 2^18 `BitVec` literals takes > 250 s and 7 GB). The chunk list is a separate
    definition so that a solver checks the chunk lengths once (`decide +kernel`) and then looks up
    a word inside one chunk instead of walking the prefix."""
    out, parts = [], []
    for i in range(0, len(ws), CHUNK):
        part = ws[i:i + CHUNK]
        n = sum(w << (bits * j) for j, w in enumerate(part))
        cn = f"{name}_{i // CHUNK}"
        parts.append(f"unpack {bits} {len(part)} {cn}")
        out.append(f"def {cn} : ℕ := 0x{n:x}")
    out.append(f"/-- Chunks of the submitted file ({len(ws)} words), {CHUNK} words each but the last. -/\n"
               f"def {name}_chunks : List (List ℕ) := [{', '.join(parts)}]")
    out.append(f"/-- Rendered from the submitted file. -/\n"
               f"def {name} : List ({ty}) := {name}_chunks.flatten.map (BitVec.ofNat {bits})")
    return out

def image(k, v, base):
    if type(v) is not dict or set(v) != {"code", "data"}:
        fail(f"{k}: expected an object with exactly the keys code, data, got {v!r}")
    code = words(confined(k, v["code"], base), 4)
    data = words(confined(k, v["data"], base), 8)
    if 4 * len(code) + 8 * len(data) > 2 ** 20:
        fail(f"{k}: image of {4 * len(code) + 8 * len(data)} bytes exceeds 2^20")
    name = k.replace(".", "_")
    out = lean_list(f"{name}_code", "BitVec 32", code, 32) + lean_list(f"{name}_data", "Word", data, 64)
    out.append(f"/-- The submitted extractor image (rendered challenge data, S4-A2). -/\n"
               f"def {name} : Image := {{ code := {name}_code, data := {name}_data }}")
    return "\n".join(out)

# ---- layouts --------------------------------------------------------------------------------

def _emitter():
    """harness/render-layout.py (the Stage 6a emitter), loaded by path."""
    here = os.path.dirname(os.path.realpath(__file__))
    spec = importlib.util.spec_from_file_location(
        "render_layout", os.path.join(here, "..", "harness", "render-layout.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

LAYOUT_HELPERS = '''/-- The element of `K` with bits `n` (layout rendering helper). -/
abbrev kx (n : ℕ) : K := ⟨BitVec.ofNat 64 n⟩

/-- A table from a list of rows; cells outside the listed rows and cells are `0`. -/
def tabOf (rows : List (List K)) : Table K := ⟨rows.length, fun r c => (rows.getD r []).getD c 0⟩

/-- The 8-bit add-with-carry table (`harness/CHAIN-LAYOUT.md`): row `r` is
`(1, x, y, cin, (x + y + cin) mod 2^8, ⌊(x + y + cin) / 2^8⌋)` with `x = r mod 2^8`,
`y = ⌊r / 2^8⌋ mod 2^8`, `cin = ⌊r / 2^16⌋`, for `r < 2^17`. -/
def add8 : Table K := ⟨2 ^ 17, fun r c =>
  let x := r % 256
  let y := r / 256 % 256
  let ci := r / 65536
  let s := x + y + ci
  match c with
  | 0 => 1 | 1 => kx x | 2 => kx y | 3 => kx ci | 4 => kx (s % 256) | 5 => kx (s / 256) | _ => 0⟩
'''

def _int(where, v, below=U64):
    if type(v) is not int or not (0 <= v < below):
        fail(f"{where}: expected a JSON integer in [0, {below}), got {v!r}")
    return v

def _kel(where, v):
    if type(v) is not str or not re.fullmatch(r"[0-9a-f]{16}", v):
        fail(f"{where}: expected a K element (16 lowercase hex digits), got {v!r}")
    return v

def _keys(where, d, required, optional=()):
    if type(d) is not dict:
        fail(f"{where}: expected an object, got {type(d).__name__}")
    missing, extra = set(required) - set(d), set(d) - set(required) - set(optional)
    if missing or extra:
        fail(f"{where}: missing keys {sorted(missing)}, unknown keys {sorted(extra)}")

def _list(where, v):
    if type(v) is not list:
        fail(f"{where}: expected a list, got {type(v).__name__}")
    return v

def check_layout(k, L):
    """Validate the layout JSON `L` (placeholder `k`); return a copy with its semantic content only
    (informational strings dropped, chips named by index)."""
    _keys(k, L, {"schema", "chips", "bus", "pub"}, {"name", "params", "busnames"})
    if L["schema"] != "recursion.fast/layout/1":
        fail(f"{k}: schema must be 'recursion.fast/layout/1', got {L['schema']!r}")
    chips = []
    for i, cj in enumerate(_list(f"{k}.chips", L["chips"])):
        w = f"{k}.chips[{i}]"
        _keys(w, cj, {"cols", "gadget", "ports", "fixed"}, {"name", "colnames"})
        cols = _int(f"{w}.cols", cj["cols"], 2 ** 32)
        g = cj["gadget"]
        _keys(f"{w}.gadget", g, {"cons", "t", "q", "M", "S", "c"}, {"names"})
        cons, t, q = (_int(f"{w}.gadget.{f}", g[f], 2 ** 32) for f in ("cons", "t", "q"))
        M = _list(f"{w}.gadget.M", g["M"])
        S = _list(f"{w}.gadget.S", g["S"])
        c = _list(f"{w}.gadget.c", g["c"])
        if len(M) != t or len(S) != q or len(c) != q:
            fail(f"{w}.gadget: |M| = {len(M)}, |S| = {len(S)}, |c| = {len(c)} for t = {t}, q = {q}")
        for j, m in enumerate(M):
            for e, ent in enumerate(_list(f"{w}.gadget.M[{j}]", m)):
                we = f"{w}.gadget.M[{j}][{e}]"
                if type(ent) is not list or len(ent) != 3:
                    fail(f"{we}: expected [row, col, K], got {ent!r}")
                _int(f"{we}.row", ent[0], cons)
                _int(f"{we}.col", ent[1], 2 * cols + 3)
                _kel(f"{we}.value", ent[2])
        for j, s in enumerate(S):
            for e, v in enumerate(_list(f"{w}.gadget.S[{j}]", s)):
                _int(f"{w}.gadget.S[{j}][{e}]", v, t)
        for j, v in enumerate(c):
            _kel(f"{w}.gadget.c[{j}]", v)
        for j, p in enumerate(_list(f"{w}.ports", cj["ports"])):
            wp = f"{w}.ports[{j}]"
            _keys(wp, p, {"bus", "send", "sel", "msg"})
            _int(f"{wp}.bus", p["bus"])
            _int(f"{wp}.sel", p["sel"])
            if type(p["send"]) is not bool:
                fail(f"{wp}.send: expected a boolean, got {p['send']!r}")
            for e, v in enumerate(_list(f"{wp}.msg", p["msg"])):
                _int(f"{wp}.msg[{e}]", v)
        fx = cj["fixed"]
        if fx is not None:
            if type(fx) is not dict or fx.get("kind") not in ("add8", "explicit"):
                fail(f"{w}.fixed: expected null, {{\"kind\": \"add8\"}} or "
                     f"{{\"kind\": \"explicit\", \"rows\": [...]}}, got {fx!r}")
            if fx["kind"] == "add8":
                _keys(f"{w}.fixed", fx, {"kind"}, {"note"})
            else:
                _keys(f"{w}.fixed", fx, {"kind", "rows"}, {"note"})
                for r, row in enumerate(_list(f"{w}.fixed.rows", fx["rows"])):
                    for e, v in enumerate(_list(f"{w}.fixed.rows[{r}]", row)):
                        _kel(f"{w}.fixed.rows[{r}][{e}]", v)
        fx = None if fx is None else {f: fx[f] for f in ("kind", "rows") if f in fx}
        chips.append({"name": str(i), "cols": cols,
                      "gadget": {f: g[f] for f in ("cons", "t", "q", "M", "S", "c")},
                      "ports": cj["ports"], "fixed": fx})
    for b, kind in enumerate(_list(f"{k}.bus", L["bus"])):
        if kind not in ("sub", "eq"):
            fail(f"{k}.bus[{b}]: expected 'sub' or 'eq', got {kind!r}")
    _int(f"{k}.pub", L["pub"])
    return {"name": k, "chips": chips, "bus": L["bus"], "pub": L["pub"]}

def layout_stats(L):
    """Chip count and total number of matrix entries (`Chip.entries` summed)."""
    return len(L["chips"]), sum(len(m) for cj in L["chips"] for m in cj["gadget"]["M"])

# ---- main -----------------------------------------------------------------------------------

def main():
    if len(sys.argv) != 4:
        fail("usage: render-challenge.py STUB.lean.in claim.json OUT.lean")
    stub, claim_path, out = sys.argv[1:4]
    sys.set_int_max_str_digits(0)
    text = open(stub).read()
    vals = strict_json(claim_path, "claim")
    if type(vals) is not dict:
        fail("claim must be a JSON object")
    found = {}
    for kind, key in PH.findall(text):
        if found.setdefault(key, kind) != kind:
            fail(f"placeholder {key} used with two types")
    if set(vals) != set(found):
        fail(f"key mismatch: missing {sorted(set(found) - set(vals))}, extra {sorted(set(vals) - set(found))}")
    base = os.path.realpath(os.path.dirname(os.path.abspath(claim_path)))
    layouts = {}
    for key, kind in found.items():
        if kind == "layout":
            if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", key):
                fail(f"layout placeholder {key}: the key must be a Lean identifier")
            L = check_layout(key, strict_json(confined(key, vals[key], base), key))
            for stat, n in zip((f"{key}.chips", f"{key}.entries"), layout_stats(L)):
                if stat in vals and vals[stat] != n:
                    fail(f"{stat}: the claim says {vals[stat]!r}, the layout {key} has {n}")
            layouts[key] = L
    helpers_done = []
    def sub(m):
        kind, key = m.groups()
        if kind == "nat": return nat(key, vals[key])
        if kind == "rat": return rat(key, vals[key])
        if kind == "hash": return hashid(key, vals[key])
        if kind == "digest": return digest(key, vals[key])
        line_start = m.string.rfind("\n", 0, m.start()) + 1
        line_end = m.string.find("\n", m.end())
        rest = m.string[m.end():] if line_end < 0 else m.string[m.end():line_end]
        if m.string[line_start:m.start()].strip() or rest.strip():
            fail(f"{kind} placeholder {key} must be on a line of its own")
        if kind == "image":
            return image(key, vals[key], base)
        lines = [] if helpers_done else [LAYOUT_HELPERS]
        helpers_done.append(key)
        lines += _emitter().layout_lean(key, layouts[key], f"{key}: the submitted layout")
        return "\n".join(lines).rstrip("\n")
    rendered = PH.sub(sub, text)
    if "{{" in rendered:
        fail("unrendered or malformed placeholder left")
    open(out, "w").write(rendered)

if __name__ == "__main__":
    main()
