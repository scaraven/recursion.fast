#!/usr/bin/env bash
# The source rule's fixtures (S6b fix pass): every `-- REJECT` line of bad/ is reported, no other
# line; good/ has no finding.  Usage: tests/source-rule/check.sh  (from anywhere)
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd)
D="$HERE/tests/source-rule"
if python3 -I "$HERE/scripts/source-rule.py" "$D/good" > /tmp/rf-srcrule-good.$$ 2>&1; then :; else
  cat /tmp/rf-srcrule-good.$$; rm -f /tmp/rf-srcrule-good.$$; echo "source rule: findings in the allowed forms"; exit 1; fi
rm -f /tmp/rf-srcrule-good.$$
got=$( { python3 -I "$HERE/scripts/source-rule.py" "$D/bad" || true; } | sed -n 's/^source-rule: Bad.lean:\([0-9]*\): .*/\1/p' | sort -un)
want=$(grep -n -- '-- REJECT$' "$D/bad/Bad.lean" | cut -d: -f1 | sort -un)
if [[ "$got" != "$want" ]]; then
  echo "source rule: reported lines differ from the -- REJECT lines"
  diff <(echo "$want") <(echo "$got") || true
  exit 1
fi
echo "source rule: $(echo "$want" | wc -l) rejected forms reported, each on its line; the allowed forms pass"
