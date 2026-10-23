#!/usr/bin/env bash
# The source rule's fixtures (S6b and S9D-M1 fix passes). Usage: tests/source-rule/check.sh
#   good/      allowed forms: no finding from either net
#   bad/       one rejected form per `-- REJECT` line: the reported lines are exactly those, and
#              each net alone (`--net lexer`, `--net raw`) reports every one of them
#   lexer/     what only a Lean-like lexer sees (constructs open at the end of the file, strings
#              whose end depends on interpolation, `r#` that is not a raw string): exact under
#              both nets, every line by the lexer, nothing by the raw scan
#   comments/  rejected words in comments and strings: exact under both nets, nothing by the
#              lexer, every line by the raw scan
#   forge/     the S9 review's lexer bypasses and the S6b forgery, verbatim: each net alone
#              reports every code line `expect.txt` lists
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd)
D="$HERE/tests/source-rule"; SR=${SOURCE_RULE:-$HERE/scripts/source-rule.py}   # SOURCE_RULE: a variant, for negative controls
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "source rule: $*"; exit 1; }
lines() {  # NET FILE: the lines the rule reports for FILE, scanned alone
  rm -rf "$T/s"; mkdir "$T/s"; cp "$2" "$T/s/"
  { python3 -I "$SR" --net "$1" "$T/s" || true; } | sed -n "s/^source-rule: $(basename "$2"):\([0-9]*\): .*/\1/p" | sort -un
}
marked() { grep -n -- '-- REJECT$' "$1" | cut -d: -f1 | sort -un; }
same() {  # what FILE NET EXPECTED
  local got; got=$(lines "$2" "$1")
  [[ "$got" == "$3" ]] || { diff <(echo "$3") <(echo "$got") || true; fail "$1 ($2 net): reported lines differ from the expected"; }
}
covers() {  # FILE NET EXPECTED: every expected line is reported
  local got miss; got=$(lines "$2" "$1"); miss=$(comm -23 <(echo "$3" | sort) <(echo "$got" | sort))
  [[ -z "$miss" ]] || fail "$1 ($2 net): not reported: $(echo $miss)"
}
n=0
for f in "$D"/good/*.lean; do same "$f" both ""; done
for f in "$D"/bad/*.lean; do
  m=$(marked "$f"); same "$f" both "$m"; covers "$f" lexer "$m"; covers "$f" raw "$m"; n=$((n + $(echo "$m" | wc -l)))
done
for f in "$D"/lexer/*.lean; do
  m=$(marked "$f"); same "$f" both "$m"; same "$f" lexer "$m"; same "$f" raw ""; n=$((n + $(echo "$m" | wc -l)))
done
for f in "$D"/comments/*.lean; do
  m=$(marked "$f"); same "$f" both "$m"; same "$f" lexer ""; same "$f" raw "$m"; n=$((n + $(echo "$m" | wc -l)))
done
k=0
while read -r file rest; do
  [[ -z "$file" || "$file" == \#* ]] && continue
  m=$(printf '%s\n' $rest | sort -un)
  covers "$D/forge/$file" lexer "$m"; covers "$D/forge/$file" raw "$m"; k=$((k + 1))
done < "$D/forge/expect.txt"
echo "source rule: $n rejected forms reported exactly (bad/: by each net alone; lexer/, comments/: by their net), $k forgeries (S9 bypasses, ForgeRaw) caught by each net alone; the allowed forms pass"
