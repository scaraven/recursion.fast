#!/usr/bin/env bash
# Regenerate harness/examples/ and RecursionFast/Controls/ChainData.lean (Stage 6a) from the
# generator. Deterministic: the example secret is the bytes 00 01 .. 1f (public, an example only);
# it is passed on stdin, as every secret is (S6a-m4). Every rendered source is kept in examples/.
#   harness/render-controls.sh            (from the repository root)
set -euo pipefail
cd "$(dirname "$0")/.."
E=harness/examples
GEN="python3 -I harness/gen-chain-layout.py"
S=000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
sec() { printf '%s\n' "$S"; }
for n in 1 4 16; do $GEN layout --n $n $E/chain-n$n.layout.json; done
for n in 1 4; do sec | $GEN witness --n $n --secret-file - $E/chain-n$n.witness.json $E/chain-n$n.stmt.json; done
sec | $GEN mini --secret-file - --call 0 $E/gcall0.layout.json $E/gcall0.witness.json $E/gcall0.stmt.json
sec | $GEN mini --secret-file - --call 79 $E/gcall79.layout.json $E/gcall79.witness.json $E/gcall79.stmt.json
sec | $GEN mini --secret-file - --call 0 --full-table \
  $E/gcall0-add8.layout.json $E/gcall0-add8.witness.json $E/gcall0-add8.stmt.json
python3 -I harness/render-layout.py RecursionFast/Controls/ChainData.lean "
# Controls data: the benchmark layout and one-G-call harnesses (Stage 6a, DESIGN §7.2)

Rendered from harness/examples/*.json (example secret 00 01 .. 1f) by harness/render-controls.sh.
The theorems are in RecursionFast/Controls/Chain.lean.

* LG0, LG79: the one-G-call harness for G-calls 0 and 79 of the chain (compression 0; call 79 has
  a zero message word), add table trimmed to the rows the witness uses (in add8 order).
* LGF: the harness for G-call 0 with the benchmark's full 2^17-row add8 table.
* Lchain: the benchmark layout L_chain(16) (no witness). L_chain(n) depends on n only through three
  constants (the last-row pins of the G chip, S0 .. S19 and FINAL, and x4 = n)." \
  LG0=$E/gcall0.layout.json,$E/gcall0.witness.json,$E/gcall0.stmt.json \
  LG79=$E/gcall79.layout.json,$E/gcall79.witness.json,$E/gcall79.stmt.json \
  LGF=$E/gcall0-add8.layout.json,$E/gcall0-add8.witness.json,$E/gcall0-add8.stmt.json \
  Lchain=$E/chain-n16.layout.json
echo "rendered RecursionFast/Controls/ChainData.lean"
