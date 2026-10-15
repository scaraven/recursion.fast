#!/usr/bin/env bash
# S6b-review probes (read-only static demonstrations; no organiser build needed).
#
# 1. sandbox-default: run-benchmark.py's "sandbox" defaults to None, and nothing requires it.
#    (probes/s6b/review/sandbox-default.py)
#        board-L config, 'sandbox' key omitted -> cfg['sandbox'] = None
#        Runner.run: 'if sb:' guard FALSE  => no --hide, no bwrap, no net/pid isolation.
#
# 2. layouts.C is not pinned to the certificate. harness.sh stage 3b builds the benchmark config
#    from the organiser's --bench FILE verbatim, injecting only verify/index:
set -euo pipefail
cd "$(dirname "$0")/../../.."
echo "# 1. sandbox default"
python3 -I probes/s6b/review/sandbox-default.py
echo
echo "# 2. harness.sh stage 3b: what it derives into the bench config (grep)"
sed -n '/stage 3b: benchmark/,/bench-config.json/p' scripts/harness.sh | sed -n '1,8p'
echo "   -> only cfg['verify'] and cfg['index'] are set from the gate tree; k, cfg, layouts.C,"
echo "      claim.{digestC,digestL} are taken from --bench FILE and never checked against the"
echo "      certificate's Declared / the rendered challenge C."
