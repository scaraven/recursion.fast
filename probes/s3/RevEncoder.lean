/- S3 review probe (compiled evaluation, not kernel): the honest tapes at arity 2/4/8/16 and the
padded Merkle root, for comparison with the independent encoder `probes/s3/indep_encoder.py`. -/
import RecursionFast.Controls.CompileToy
open RecursionFast RecursionFast.Controls.Compile

def cfg8 : Cfg := ⟨.blake2s, 8, by decide⟩
def cfg16 : Cfg := ⟨.blake2s, 16, by decide⟩

#eval [cfg2, cfg4, cfg8, cfg16].map fun c =>
  (c.arity, (prove c cmpToy L0 x0 []).map (fun t => (t.length, toHex t)),
   toHex (index c cmpToy L0).2,
   (prove c cmpToy L0 x0 []).map (NARG c cmpToy (index c cmpToy L0) x0))
-- An internal node whose children are all padding: 8 leaves at arity 4 (depth 2, 16 positions).
#eval toHex (commit cfg4 ⟨⟨3, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩⟩)
-- Depth at every arity for 1..2^6 leaves (the `find?` in `Cfg.depth`).
#eval [cfg2, cfg4, cfg8, cfg16].map fun c => (List.range 7).map fun m => c.depth ⟨m, 0⟩
