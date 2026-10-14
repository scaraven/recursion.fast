#!/usr/bin/env bash
# A4-F5: the renderer must reject every malformed claim (and accept the well-formed one).
set -uo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
stub=RecursionFast/Challenge/T1.lean.in
python3 scripts/dummy-claim.py $stub "$tmp/ok.json"
python3 scripts/render-challenge.py $stub "$tmp/ok.json" "$tmp/ok.lean" || { echo "render: well-formed claim rejected"; exit 1; }
bad() {  # name, python expression mutating dict d
  python3 -I -c "import json,sys; d=json.load(open(sys.argv[1])); $2; json.dump(d,open(sys.argv[2],'w'))" "$tmp/ok.json" "$tmp/$1.json"
  if python3 scripts/render-challenge.py $stub "$tmp/$1.json" "$tmp/$1.lean" 2>"$tmp/$1.err"; then
    echo "render: $1 ACCEPTED (bug)"; exit 1; else echo "render: $1 rejected: $(tail -1 "$tmp/$1.err")"; fi; }
bad bool        'd["c16.add"]=True'
bad extra_key   'd["extra.unused"]=5'
bad missing_key 'del d["c20.qBytes"]'
bad too_large   'd["c24.st"]=2**64'
bad negative    'd["c24.st"]=-1'
bad float       'd["c16.sys"]=1.5'
bad rat_syntax  'd["zk4"]="1/0"'
bad rat_inject  'd["zk4"]="1) + (2"'
bad rat_as_int  'd["zk4"]=7'
bad harts_int   'd["image"]["harts"]=1'
bad image_keys  'd["image"]["extra"]="x"'
head -c 1048580 /dev/zero > "$tmp/big.code"
bad image_big   "d['image']['code']='big.code'"
printf 'abc' > "$tmp/odd.code"
bad image_odd   "d['image']['code']='odd.code'"
# A6-R1: image paths are confined to the claim's directory (absolute, `..`, symlinks rejected).
mkdir -p "$tmp/outside"; printf 'SECRET-HARNESS-TOKEN-0123456789a' > "$tmp/outside/secret.bin"
ln -s "$tmp/outside/secret.bin" "$tmp/link-out.code"; ln -s toy.code "$tmp/link-in.code"
mkdir -p "$tmp/sub"; ln -s "$tmp/outside" "$tmp/sub/dir"
bad path_abs     "d['image']['code']='$tmp/outside/secret.bin'"
bad path_dotdot  "d['image']['data']='../$(basename "$tmp")/outside/secret.bin'"
bad path_dot     "d['image']['code']='./toy.code'"
bad path_link    "d['image']['code']='link-out.code'"
bad path_link_in "d['image']['code']='link-in.code'"
bad path_linkdir "d['image']['code']='sub/dir/secret.bin'"
bad path_dir     "d['image']['code']='outside'"
# the A6 probe claims (probes/a6/render): an absolute path and a `../../..` path
for c in claim-traversal claim; do
  if python3 scripts/render-challenge.py $stub probes/a6/render/$c.json "$tmp/$c.lean" 2>"$tmp/$c.err"; then
    echo "render: A6 probe $c ACCEPTED (bug)"; exit 1; else echo "render: A6 probe $c rejected: $(tail -1 "$tmp/$c.err")"; fi
done
echo "render tests OK"
