"""S3 review: input-length domains of every hash call in `Contract/Compile.lean`.
tree: leaf 8*2^logLeaf (logLeaf <= k+10 <= 38), node 32*A (A in 2,4,8,16)
sponge: absorb 1+32+|m| with |m| in {32 (root), 256 (x), 8*2^logLen (plain)}, squeeze 1+32
key digest (seed's first hash, = D of DESIGN 5.1): 8*vkLen + 32, vkLen <= 2^10.
Usage: python3 -I domains.py"""
A_S = (2, 4, 8, 16)
leaf = {8 * 2**l: f"leaf(logLeaf={l})" for l in range(0, 39)}
node = {32 * A: f"node(A={A})" for A in A_S}
absorb = {33 + 32: "absorb(root)", 33 + 256: "absorb(x)"} | {33 + 8 * 2**l: f"absorb(plain logLen={l})" for l in range(0, 39)}
squeeze = {33: "squeeze"}
key = {8 * v + 32: f"key(vkLen={v})" for v in range(0, 2**10 + 1)}
tree = leaf | {}
print("leaf/node length coincidences (2^logLeaf = 4A):",
      sorted((node[n], leaf[n]) for n in node if n in leaf))
print("tree vs sponge coincidences:", [n for n in (set(leaf) | set(node)) if n in absorb or n in squeeze])
print("residues mod 8: tree", {n % 8 for n in list(leaf) + list(node)}, "sponge", {n % 8 for n in list(absorb) + list(squeeze)},
      "key", {n % 8 for n in key})
print("key digest vs node:", sorted(key[n] + " = " + node[n] for n in key if n in node))
print("key digest vs leaf:", sorted(key[n] + " = " + leaf[n] for n in key if n in leaf))
print("key digest vs sponge:", [n for n in key if n in absorb or n in squeeze])
# BLAKE2s compressions of a leaf with and without a 1-byte tag
blocks = lambda n: max(1, -(-n // 64))
print("leaf compressions (logLeaf: untagged -> tagged):", {l: (blocks(8 * 2**l), blocks(8 * 2**l + 1)) for l in range(0, 8)})
