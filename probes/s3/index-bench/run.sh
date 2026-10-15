#!/usr/bin/env bash
# S9 compile fix pass: build the indexing benchmark against the organiser package ORG (here: the
# repository itself) in the scratch tree W, then time `index`.   run.sh ORG REPO W LAYOUT WHICH...
set -euo pipefail
ORG=$1; REPO=$2; W=$3; LAYOUT=$4; shift 4; HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$W"; rm -rf "$W/submission" "$W/badge"; cp -r "$HERE/src/submission" "$HERE/src/badge" "$W/"
python3 -I "$REPO/harness/mk-tree.py" "$ORG" "$W" S3IdxBench
cp "$REPO/lean-toolchain" "$W/"
# path packages of ORG's manifest are relative to ORG (ext/Clean): make them absolute here
python3 -I -c "import json,os,sys; w,o=sys.argv[1:]; m=json.load(open(w+'/lake-manifest.json'))
for p in m['packages']:
    d=p.get('dir')
    if d and not os.path.isabs(d): p['dir']=os.path.normpath(os.path.join(o,d))
json.dump(m,open(w+'/lake-manifest.json','w'),indent=1)" "$W" "$ORG"
(cd "$W" && lake build harness-idx 2>&1 | grep -E "error|Build" | tail -3)
for w in "$@"; do (cd "$W" && /usr/bin/time -f "  %e s wall, %M KB" .lake/build/bin/harness-idx "$LAYOUT" "$w"); done
