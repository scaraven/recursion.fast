"""S3 review: compare `indep_encoder.py` with the Lean evaluations logged by `RevEncoder.lean`.
Usage: python3 -I cmp_encoder.py logs/S3-review/rev-encoder.log probes/s3/indep_encoder.py"""
import re, sys, subprocess
log = open(sys.argv[1]).read()
lean = re.findall(r'\((\d+),\s*some\s*\((\d+),\s*"([0-9a-f]+)"\),\s*"([0-9a-f]+)", some true\)', log)
out = subprocess.run([sys.executable, "-I", sys.argv[2]], capture_output=True, text=True).stdout
py = {}
for m in re.finditer(r'arity (\d+): i=\d+ len=(\d+) index_root=([0-9a-f]+)\n  tape ([0-9a-f]+)', out):
    py[int(m.group(1))] = (int(m.group(2)), m.group(4), m.group(3))
for A, n, t, r in lean:
    A = int(A); n = int(n)
    print(A, "len", n == py[A][0], "tape", t == py[A][1], "index_root", r == py[A][2])
pad = re.search(r'^"([0-9a-f]{64})"$', log, re.M).group(1)
m = re.search(r'pad_internal_zero=False: root\(8 leaves, A=4\)=([0-9a-f]+)', out).group(1)
z = re.search(r'pad_internal_zero=True: root\(8 leaves, A=4\)=([0-9a-f]+)', out).group(1)
print("padded root: lean == literal-reading", pad == m, "; lean == zero-subtree reading", pad == z)
