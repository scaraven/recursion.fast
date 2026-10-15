#!/usr/bin/env python3
"""render-layout.py: render layout / witness / statement JSON (harness/README.md) as Lean definitions.

  python3 -I harness/render-layout.py OUT.lean MODULE_DOC NAME=LAYOUT.json[,WITNESS.json,STMT.json] ...

For each `NAME=…` argument it emits, in namespace `RecursionFast.Controls.Chain`:

  def NAME_chipI : Chip K          (one per chip)
  def NAME : Layout K              (the layout)
  def NAME_wit : List (Table K)    (if a witness is given)
  def NAME_stmt : Fin 32 → K       (if a statement is given)

K elements are written `kx 0x…` (`kx n = ⟨BitVec.ofNat 64 n⟩`); explicit tables are `tabOf rows`
(missing cells 0); the table kind `add8` is the closed-form `add8` of the output's preamble. The
rendering is purely syntactic: every number is copied from the JSON, nothing is evaluated.
"""
import hashlib, json, sys

PREAMBLE = '''import RecursionFast.Contract.Layout
import Mathlib.Data.Fin.VecNotation

namespace RecursionFast.Controls.Chain
open RecursionFast

/-- The element of `K` with bits `n`. -/
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


def kx(h):
    """A K element: exactly 16 lowercase hex digits (the schema of harness/README.md)."""
    if type(h) is not str or len(h) != 16 or any(ch not in "0123456789abcdef" for ch in h):
        raise SystemExit(f"render: not a K element (16 lowercase hex digits): {h!r}")
    v = int(h, 16)
    return f"kx 0x{v:x}" if v > 9 else f"kx {v}"


def rows_lean(rows, ind):
    out = []
    for r in rows:
        out.append(ind + "[" + ", ".join(kx(v) for v in r) + "]")
    return "[\n" + ",\n".join(out) + "]"


def table_lean(spec, ind="    "):
    if "kind" in spec:
        if spec["kind"] == "add8":
            if spec.get("extra"):
                raise SystemExit("render: add8 with extra rows is not rendered")
            return "add8"
        if spec["kind"] == "explicit":
            return "tabOf " + rows_lean(spec["rows"], ind)
        raise SystemExit(f"render: unknown table kind {spec['kind']}")
    if spec["rows"] != len(spec["cells"]):        # the witness schema: `rows` = the listed rows
        raise SystemExit(f"render: rows {spec['rows']} but {len(spec['cells'])} rows listed")
    return "tabOf " + rows_lean(spec["cells"], ind)


def chip_lean(name, i, cj):
    g = cj["gadget"]
    cons, t, q, cols = g["cons"], g["t"], g["q"], cj["cols"]
    lines = [f"/-- Chip {i} of `{name}`: `{cj.get('name', i)}`, {cols} columns. -/",
             f"def {name}_chip{i} : Chip K where",
             f"  cols := {cols}"]
    if t == 0 and q == 0:
        lines.append(f"  gadget := ⟨{cons}, 0, Fin.elim0, 0, Fin.elim0, Fin.elim0⟩")
    else:
        ms = []
        for m in g["M"]:
            ents = [f"({r}, {c}, {kx(v)})" for r, c, v in m]
            body = ",\n      ".join(", ".join(ents[k:k + 6]) for k in range(0, len(ents), 6))
            ms.append("[" + body + "]")
        S = ", ".join("[" + ", ".join(str(j) for j in s) + "]" for s in g["S"])
        C = ", ".join(kx(v) for v in g["c"])
        lines.append("  gadget :=")
        lines.append(f"    {{ cons := {cons}, t := {t}, q := {q},")
        lines.append("      M := ![" + ",\n        ".join(ms) + "],")
        lines.append(f"      S := ![{S}], c := ![{C}] }}")
    ports = ", ".join(f"⟨{p['bus']}, {'true' if p['send'] else 'false'}, {p['sel']}, "
                      f"[{', '.join(str(c) for c in p['msg'])}]⟩" for p in cj["ports"])
    lines.append(f"  ports := [{ports}]")
    fx = cj["fixed"]
    lines.append("  fixed := " + ("none" if fx is None else "some (" + table_lean(fx) + ")"))
    return "\n".join(lines)


def render(name, lp, wp, xp, src):
    L = json.load(open(lp))
    out = [f"/-! ## `{name}`: {L.get('name', '')} (`{src[lp]}`) -/", ""]
    for i, cj in enumerate(L["chips"]):
        out.append(chip_lean(name, i, cj))
        out.append("")
    kinds = ", ".join("." + k for k in L["bus"])
    chips = ", ".join(f"{name}_chip{i}" for i in range(len(L["chips"])))
    out.append(f"/-- The layout `{L.get('name', name)}`: bus `b` has kind `[{kinds}][b]` (`.eq` beyond). -/")
    out.append(f"def {name} : Layout K :=\n  ⟨[{chips}],\n   fun b => ([{kinds}] : List BusKind).getD b .eq, {L['pub']}⟩")
    out.append("")
    if wp:
        W = json.load(open(wp))
        tabs = ",\n  ".join(table_lean(t) for t in W["tables"])
        out.append(f"/-- The witness (`{src[wp]}`). -/")
        out.append(f"def {name}_wit : List (Table K) := [\n  {tabs}]")
        out.append("")
    if xp:
        X = json.load(open(xp))
        xs = ", ".join(kx(v) for v in X["x"])
        out.append(f"/-- The statement (`{src[xp]}`). -/")
        out.append(f"def {name}_stmt : Fin 32 → K := fun i => ([{xs}] : List K).getD i 0")
        out.append("")
    return "\n".join(out)


def main():
    if len(sys.argv) < 4:
        raise SystemExit(__doc__)
    outp, doc = sys.argv[1], sys.argv[2]
    parts, src = [], {}
    for arg in sys.argv[3:]:
        name, _, files = arg.partition("=")
        fs = files.split(",")
        lp, wp, xp = (fs + [None, None])[:3]
        for f in (lp, wp, xp):
            if f:
                src[f] = f.split("/")[-1] + " sha256 " + hashlib.sha256(open(f, "rb").read()).hexdigest()[:16]
        parts.append(render(name, lp, wp, xp, src))
    header = "/-\n" + doc.strip() + "\n\nGenerated by `harness/render-layout.py`; do not edit by hand.\n-/\n"
    with open(outp, "w") as f:
        f.write(header + PREAMBLE + "\n" + "\n".join(parts) + "\nend RecursionFast.Controls.Chain\n")


if __name__ == "__main__":
    main()
