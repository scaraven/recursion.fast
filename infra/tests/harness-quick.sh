#!/bin/bash
# The harness's quick tests inside a runner VM (rf-supervisor test bench harness-quick.sh --tar
# core.tar): the workflow's runner-setup.sh, tests/harness/test_aggregate.py, the service build
# (cargo, the repository's toolchain) and tests/harness/test_sandbox.py against it.
set -uo pipefail
cd ~/core
export GITHUB_ENV=$HOME/github_env
bash harness/ci/runner-setup.sh; echo "runner-setup.sh: exit $?"
set -a; source "$GITHUB_ENV"; set +a
timeout 600 python3 -I tests/harness/test_aggregate.py > ~/agg.log 2>&1; echo "test_aggregate.py: exit $?"; tail -3 ~/agg.log
(cd service && timeout 900 cargo build --release -q); echo "cargo build --release: exit $?"
timeout 1200 python3 tests/harness/test_sandbox.py "$PWD/service/target/release/rf-oracle" > ~/sandbox.log 2>&1; echo "test_sandbox.py: exit $?"; tail -15 ~/sandbox.log
