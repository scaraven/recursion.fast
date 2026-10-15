#!/usr/bin/env python3
"""Write a dummy claim for a challenge stub (CI: every stub must render and elaborate).

  python3 -I scripts/dummy-claim.py STUB.lean.in OUT/claim.json

Every nat is 7 (a layout's `KEY.chips` / `KEY.entries` are its own counts), every rat "7", every
hash "blake2s", every digest 32 zero bytes, every image the 8-instruction first-message image
(`Library/Extractor.lean`, `firstMsgImg`) and every layout a one-chip layout (a public chip of 32
columns, no constraint, no port); the files are written next to the claim (the renderer reads only
files inside the claim's directory, A6-R1)."""
import json, os, re, struct, sys

FIRST_MSG = [0x00100313, 0x03f31313, 0x03833503, 0x04033583, 0x00351513, 0x00650533, 0x00000293,
             0x00000073]
TINY = {"schema": "recursion.fast/layout/1", "name": "dummy (one public chip)",
        "chips": [{"name": "PUB", "cols": 32,
                   "gadget": {"cons": 0, "t": 0, "q": 0, "M": [], "S": [], "c": []},
                   "ports": [], "fixed": None}],
        "bus": [], "pub": 0}

stub, out = sys.argv[1:3]
outdir = os.path.dirname(os.path.abspath(out))
d, layouts = {}, set()
for kind, key in re.findall(r"\{\{(nat|rat|hash|digest|image|layout):([A-Za-z0-9_.]+)\}\}", open(stub).read()):
    if kind == "nat": d[key] = 7
    elif kind == "rat": d[key] = "7"
    elif kind == "hash": d[key] = "blake2s"
    elif kind == "digest": d[key] = "00" * 32
    elif kind == "image":
        with open(os.path.join(outdir, "dummy.code"), "wb") as f: f.write(struct.pack("<8I", *FIRST_MSG))
        open(os.path.join(outdir, "dummy.data"), "wb").close()
        d[key] = {"code": "dummy.code", "data": "dummy.data"}
    else:
        json.dump(TINY, open(os.path.join(outdir, f"dummy-{key}.layout.json"), "w"))
        d[key] = f"dummy-{key}.layout.json"
        layouts.add(key)
for key in layouts:
    if f"{key}.chips" in d: d[f"{key}.chips"] = 1
    if f"{key}.entries" in d: d[f"{key}.entries"] = 0
json.dump(d, open(out, "w"), indent=1)
