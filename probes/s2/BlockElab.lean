import RecursionFast.Contract.Hash.Blake2s
set_option pp.coercions false
#print RecursionFast.Blake2s.block
#eval (RecursionFast.Blake2s.block ((List.range 70).map Nat.toUInt8)).toList.map (fun w => w.toNat)
