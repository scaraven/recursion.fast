#!/usr/bin/env bash
# A4-F5, A6-R1, S6b: the renderer must reject every malformed claim and accept the well-formed ones.
#   scripts/test-render.sh [OUTDIR]     (OUTDIR keeps the well-formed renderings, for elaboration)
# Board L stub: nat / hash / image placeholders; board R stub: also digest and layout placeholders.
set -uo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
OUT=${1:-$tmp/out}; mkdir -p "$OUT"
R="python3 -I scripts/render-challenge.py"
L_STUB=RecursionFast/Challenge/L.lean.in
R_STUB=RecursionFast/Challenge/R.lean.in
python3 -I scripts/dummy-claim.py $L_STUB "$tmp/L.json"
python3 -I scripts/dummy-claim.py $R_STUB "$tmp/R.json"
# the well-formed R claim with a real layout: the benchmark layout L_chain(16) as C
cp harness/examples/chain-n16.layout.json "$tmp/chain16.json"
python3 -I - "$tmp/R.json" "$tmp/Rchain.json" "$tmp/chain16.json" <<'EOF'
import json, sys
d = json.load(open(sys.argv[1])); L = json.load(open(sys.argv[3]))
d["C"] = "chain16.json"; d["C.chips"] = len(L["chips"])
d["C.entries"] = sum(len(m) for c in L["chips"] for m in c["gadget"]["M"])
json.dump(d, open(sys.argv[2], "w"))
EOF
for c in L:$L_STUB R:$R_STUB Rchain:$R_STUB; do
  n=${c%%:*} s=${c#*:}
  $R $s "$tmp/$n.json" "$OUT/$n.lean" || { echo "render: well-formed claim $n rejected"; exit 1; }
  echo "render: well-formed claim $n accepted"
done
fails=0
bad() {  # name, stub, base claim, python statement mutating dict d (and possibly writing files)
  local n=$1 stub=$2 base=$3
  python3 -I -c "import json,sys,os; os.chdir(sys.argv[3]); d=json.load(open(sys.argv[1])); $4; json.dump(d,open(sys.argv[2],'w'))" \
    "$tmp/$base.json" "$tmp/$n.json" "$tmp" || { echo "test-render: mutation $n failed"; exit 1; }
  if $R $stub "$tmp/$n.json" "$tmp/$n.lean" 2>"$tmp/$n.err"; then
    echo "render: $n ACCEPTED (bug)"; fails=1; else echo "render: $n rejected: $(tail -1 "$tmp/$n.err")"; fi; }
lbad() { bad "$1" $L_STUB L "$2"; }
# a layout mutation: load the chain layout, apply the statement to `L`, write it as `$1.layout.json`
lay() { bad "$1" $R_STUB Rchain "L=json.load(open('chain16.json')); $2; json.dump(L,open('$1.layout.json','w')); d['C']='$1.layout.json'"; }
# -- scalars (board L)
lbad bool        'd["k"]=True'
lbad extra_key   'd["extra"]=5'
lbad missing_key 'del d["arity"]'
lbad too_large   'd["k"]=2**64'
lbad negative    'd["k"]=-1'
lbad float       'd["arity"]=2.0'
lbad nat_string  'd["k"]="20"'
lbad hash_menu   'd["hash"]="sha256"'
lbad hash_case   'd["hash"]="BLAKE2s"'
lbad hash_int    'd["hash"]=1'
printf '{"k": 20, "k": 21}' > "$tmp/dup.json"
if $R $L_STUB "$tmp/dup.json" "$tmp/dup.lean" 2>"$tmp/dup.err"; then echo "render: dup_key ACCEPTED (bug)"; fails=1
else echo "render: dup_key rejected: $(tail -1 "$tmp/dup.err")"; fi
# -- image
lbad image_harts 'd["image"]["harts"]=False'
lbad image_keys  'd["image"]={"code": "dummy.code"}'
head -c 1048580 /dev/zero > "$tmp/big.code"
lbad image_big   "d['image']['code']='big.code'"
printf 'abc' > "$tmp/odd.code"
lbad image_odd   "d['image']['code']='odd.code'"
# -- paths (A6-R1): absolute, `..`, `./`, symlinks out / in / through a directory, a directory
mkdir -p "$tmp/outside"; printf 'SECRET-HARNESS-TOKEN-0123456789a' > "$tmp/outside/secret.bin"
ln -s "$tmp/outside/secret.bin" "$tmp/link-out.code"; ln -s dummy.code "$tmp/link-in.code"
mkdir -p "$tmp/sub"; ln -s "$tmp/outside" "$tmp/sub/dir"
lbad path_abs     "d['image']['code']='$tmp/outside/secret.bin'"
lbad path_dotdot  "d['image']['data']='../$(basename "$tmp")/outside/secret.bin'"
lbad path_dot     "d['image']['code']='./dummy.code'"
lbad path_link    "d['image']['code']='link-out.code'"
lbad path_link_in "d['image']['code']='link-in.code'"
lbad path_linkdir "d['image']['code']='sub/dir/secret.bin'"
lbad path_dir     "d['image']['code']='outside'"
lbad path_deep    "d['image']['code']='../../../../../../../../etc/passwd'"
# -- digests (board R)
bad digest_upper $R_STUB R 'd["digestC"]="AB"*32'
bad digest_short $R_STUB R 'd["digestL"]="00"*31'
bad digest_list  $R_STUB R 'd["digestC"]=[0]*32'
# -- layouts (board R): path, JSON, schema, ranges (a Fin literal would wrap), lengths, kinds
bad layout_abs   $R_STUB Rchain "d['C']='$tmp/chain16.json'"
bad layout_obj   $R_STUB Rchain "d['C']=json.load(open('chain16.json'))"
printf 'not json' > "$tmp/notjson.layout.json"
bad layout_text  $R_STUB Rchain "d['C']='notjson.layout.json'"
printf '{"schema": "recursion.fast/layout/1", "chips": [], "chips": [], "bus": [], "pub": 0}' > "$tmp/dup.layout.json"
bad layout_dup   $R_STUB Rchain "d['C']='dup.layout.json'"
printf '{"schema": "recursion.fast/layout/1", "chips": [], "bus": [], "pub": 0.0}' > "$tmp/float.layout.json"
bad layout_float $R_STUB Rchain "d['C']='float.layout.json'"
printf '{"schema": "recursion.fast/layout/1", "chips": [], "bus": [], "pub": NaN}' > "$tmp/nan.layout.json"
bad layout_nan   $R_STUB Rchain "d['C']='nan.layout.json'"
lay schema       'L["schema"]="recursion.fast/layout/0"'
lay unknown_key  'L["chips"][1]["evil"]=1'
lay missing_key  'del L["chips"][1]["ports"]'
lay row_range    'L["chips"][1]["gadget"]["M"][0][0][0]=L["chips"][1]["gadget"]["cons"]'
lay col_range    'g=L["chips"][1]; g["gadget"]["M"][0][0][1]=2*g["cols"]+3'
lay S_range      'g=L["chips"][1]["gadget"]; g["S"][0][0]=g["t"]'
lay M_length     'g=L["chips"][1]["gadget"]; g["M"].append([])'
lay c_length     'g=L["chips"][1]["gadget"]; g["c"].append("0000000000000001")'
lay K_upper      'g=L["chips"][1]["gadget"]; g["c"][0]=g["c"][0].upper().replace("0","A")'
lay K_short      'g=L["chips"][1]["gadget"]; g["c"][0]="01"'
lay K_int        'g=L["chips"][1]["gadget"]; g["M"][0][0][2]=1'
lay entry_shape  'g=L["chips"][1]["gadget"]; g["M"][0][0]=g["M"][0][0][:2]'
lay send_int     'L["chips"][1]["ports"][0]["send"]=1'
lay bus_kind     'L["bus"][0]="lookup"'
lay fixed_kind   'L["chips"][2]["fixed"]={"kind": "add16"}'
lay fixed_extra  'L["chips"][2]["fixed"]={"kind": "add8", "extra": [["0000000000000000"]]}'
lay fixed_rowK   'L["chips"][3]["fixed"]["rows"][0][0]="x"'
lay pub_neg      'L["pub"]=-1'
lay cols_bool    'L["chips"][0]["cols"]=True'
bad chips_count  $R_STUB Rchain 'd["C.chips"]+=1'
bad entries_count $R_STUB Rchain 'd["C.entries"]-=1'
# informational strings never reach the output (they would sit inside a Lean comment)
python3 -I -c "import json,sys; L=json.load(open(sys.argv[1])); L['name']='x -/ theorem evil : False := sorry /-'; L['chips'][0]['name']='-/ #eval 1 /-'; json.dump(L,open(sys.argv[2],'w'))" \
  "$tmp/chain16.json" "$tmp/inject.layout.json"
python3 -I -c "import json,sys; d=json.load(open(sys.argv[1])); d['C']='inject.layout.json'; json.dump(d,open(sys.argv[2],'w'))" "$tmp/Rchain.json" "$tmp/inject.json"
if $R $R_STUB "$tmp/inject.json" "$tmp/inject.lean" && ! grep -q "evil\|#eval" "$tmp/inject.lean"; then
  echo "render: informational strings dropped (comment injection impossible)"
else echo "render: informational strings reached the output (bug)"; fails=1; fi
# a line placeholder must be on its own line
sed 's/^{{layout:C}}$/def junk := 0 {{layout:C}}/' $R_STUB > "$tmp/inline.lean.in"
if $R "$tmp/inline.lean.in" "$tmp/Rchain.json" "$tmp/inline.lean" 2>"$tmp/inline.err"; then echo "render: inline_layout ACCEPTED (bug)"; fails=1
else echo "render: inline_layout rejected: $(tail -1 "$tmp/inline.err")"; fi
[[ $fails -eq 0 ]] || { echo "render tests FAILED"; exit 1; }
echo "render tests OK"
