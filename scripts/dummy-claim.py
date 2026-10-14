#!/usr/bin/env python3
"""Write a dummy claim for a stub (CI: every stub must render and elaborate): every nat = 7,
every rat = "7", every image = the toy image files (audit/toy.code, audit/toy.data), copied next
to the claim (the renderer only reads files inside the claim's directory, A6-R1)."""
import json, os, re, shutil, sys
stub, out = sys.argv[1:3]
d = {}
audit = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "audit")
outdir = os.path.dirname(os.path.abspath(out))
for f in ("toy.code", "toy.data"):
    shutil.copyfile(os.path.join(audit, f), os.path.join(outdir, f))
for kind, key in re.findall(r"\{\{(nat|rat|image):([A-Za-z0-9_.]+)\}\}", open(stub).read()):
    d[key] = 7 if kind == "nat" else "7" if kind == "rat" else {"code": "toy.code", "data": "toy.data", "harts": False}
json.dump(d, open(out, "w"))
