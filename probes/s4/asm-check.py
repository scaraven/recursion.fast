#!/usr/bin/env python3
"""S4 review probe: re-assemble tests/asm/*.S and compare with the committed .bin files and
with the instruction-word literals of Controls/ and Library/Extractor.lean; likewise the review's
own images (probes/s4/asm) against ChainBudget.lean and MachineEdge.lean. Each assembled program
must occur as one literal (a .bin, where present, must match)."""
import os, re, struct, subprocess, sys, tempfile
root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
dirs = [os.path.join(root, "tests", "asm"), os.path.join(root, "probes", "s4", "asm")]
lean = "".join(open(os.path.join(root, f)).read() for f in [
    "RecursionFast/Controls/Extractor.lean", "RecursionFast/Library/Extractor.lean",
    "probes/s4/ChainBudget.lean", "probes/s4/MachineEdge.lean"])
ok = True
for asm, f in sorted((d, f) for d in dirs for f in os.listdir(d)):
    if not f.endswith(".S"): continue
    name = f[:-2]
    with tempfile.TemporaryDirectory() as d:
        o, b = os.path.join(d, "a.o"), os.path.join(d, "a.bin")
        subprocess.run(["riscv64-unknown-elf-as", "-march=rv64im_zbc_zicsr_zicntr", "-o", o,
                        os.path.join(asm, f)], check=True)
        subprocess.run(["riscv64-unknown-elf-objcopy", "-O", "binary", "-j", ".text", o, b], check=True)
        data = open(b, "rb").read()
    words = list(struct.unpack(f"<{len(data)//4}I", data))
    binf = os.path.join(asm, name + ".bin")
    same_bin = (not os.path.exists(binf)) or open(binf, "rb").read() == data
    # every word-list literal in the Lean controls/library; is this program one of them?
    lits = [[int(x, 16) for x in re.findall(r"0x[0-9a-f]+", g)]
            for g in re.findall(r"\[((?:0x[0-9a-f]+,\s*)*0x[0-9a-f]+)\]", lean)]
    lit = words if words in lits else None
    same_lit = lit is not None
    print(f"{name:10s} {len(words):3d} instr  bin={'OK' if same_bin else 'DIFF'}  lean={'OK' if same_lit else 'NOT FOUND'}")
    ok &= same_bin and same_lit
sys.exit(0 if ok else 1)
