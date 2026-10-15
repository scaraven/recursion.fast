#!/usr/bin/env python3
"""The v2 toy comparator pair (Stage 6b; v0.3's audit/ToySolution.lean, re-made for v2).

  python3 -I scripts/toy-solution.py OUTDIR

Writes into OUTDIR: the toy claim (`toy-claim.json`: class 20, BLAKE2s, arity 2, the extractor
image `firstmsg.code`/`firstmsg.data` = `Library/Extractor.lean`'s 8-instruction `firstMsgImg`,
written here from its words: no binary in git), the challenge rendered from the production board-L
stub `RecursionFast/Challenge/L.lean.in` (`ToyChallenge.lean`), the solution (`ToySolution.lean`:
the same organiser definitions verbatim, the secure toy protocol `Controls.toy20` at arity 2, the
certificate) and a negative solution (`ToySolutionBad.lean`: one word of the rendered image
changed, A4-F2; the comparator must reject it). CI compares them with the committed audit/ copies.
"""
import json, os, struct, subprocess, sys

FIRST_MSG = [0x00100313, 0x03f31313, 0x03833503, 0x04033583, 0x00351513, 0x00650533, 0x00000293,
             0x00000073]
here = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "firstmsg.code"), "wb") as f:
    f.write(struct.pack(f"<{len(FIRST_MSG)}I", *FIRST_MSG))
open(os.path.join(out, "firstmsg.data"), "wb").close()
claim = {"k": 20, "hash": "blake2s", "arity": 2, "image": {"code": "firstmsg.code", "data": "firstmsg.data"}}
with open(os.path.join(out, "toy-claim.json"), "w") as f:
    json.dump(claim, f, indent=1)
    f.write("\n")
ch = os.path.join(out, "ToyChallenge.lean")
subprocess.run([sys.executable, "-I", os.path.join(here, "scripts", "render-challenge.py"),
                os.path.join(here, "RecursionFast", "Challenge", "L.lean.in"), os.path.join(out, "toy-claim.json"), ch],
               check=True)
s = open(ch).read()
s = s.replace("import RecursionFast.Contract\n", "import RecursionFast.Contract\nimport RecursionFast.Controls.Toy\n", 1)
s = s.replace("def submission : Submission declared.k := sorry",
              "def submission : Submission declared.k := ⟨Controls.toy20, ⟨.blake2s, 2, by decide⟩, Controls.toy20_secure⟩", 1)
s = s.replace("theorem certified : Certificate declared submission := sorry",
              "theorem certified : Certificate declared submission :=\n  ⟨⟨rfl, rfl⟩, rfl⟩", 1)
assert "sorry" not in s.split("-/", 1)[1], "unreplaced sorry"
s = s.replace("/-\n  Challenge stub, board L", "/-\n  TOY SOLUTION (comparator demonstration, CI), from the challenge stub, board L", 1)
open(os.path.join(out, "ToySolution.lean"), "w").write(s)
bad = s.replace("def image_code_0 : ℕ := 0x73", "def image_code_0 : ℕ := 0x63", 1)
bad = bad.replace("⟨⟨rfl, rfl⟩, rfl⟩", "⟨⟨rfl, rfl⟩, sorry⟩", 1)
assert bad != s
open(os.path.join(out, "ToySolutionBad.lean"), "w").write(
    "-- NEGATIVE comparator test (not a default target): one word of the rendered image is changed.\n" + bad)
