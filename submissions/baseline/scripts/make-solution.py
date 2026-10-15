#!/usr/bin/env python3
"""Make audit/BaselineSolution.lean from the rendered challenge audit/BaselineChallenge.lean (Stage 6b's
RecursionFast/Challenge/L.lean.in, rendered by scripts/render-challenge.py): the same
organiser definitions verbatim, `submission := RecursionFastCandidate.submission 24 h24`, and the proof
`⟨⟨rfl, rfl⟩, rfl⟩`: the rendered configuration and extractor image (`declared`, whose `img` is the
rendered `image`, S7-A1) are definitionally the candidate's.

  python3 -I make-solution.py CHALLENGE.lean OUT.lean
"""
import sys
src, out = sys.argv[1:3]
s = open(src).read()
s = s.replace("import RecursionFast.Contract\n", "import RecursionFast.Contract\nimport RecursionFastCandidate\n", 1)
old = "def submission : Submission declared.k := sorry"
assert s.count(old) == 1, "no submission placeholder"
s = s.replace(old, "def submission : Submission declared.k :=\n  RecursionFastCandidate.submission 24 RecursionFastCandidate.h24", 1)
old = "theorem certified : Certificate declared submission := sorry"
assert s.count(old) == 1, "no certified placeholder"
s = s.replace(old, "theorem certified : Certificate declared submission :=\n  ⟨⟨rfl, rfl⟩, rfl⟩", 1)
assert "sorry" not in s.split("-/", 1)[1], "unreplaced sorry"
open(out, "w").write(s)
