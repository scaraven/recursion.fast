/-
  The executable reference signer (V4-A4), for testing the service against the Lean signer.

    lake -f scripts/speed/lakefile.toml build signer
    .lake/build/bin/signer <seed-hex> <j> <message-hex>

  `seed-hex`: the 32-byte signing seed; `j`: the one-time key index (below 2^16); `message-hex`:
  the 32-byte message (a trace digest). Output, one lowercase hex string per line: the public
  key `vk`, then the signature as `idx` (decimal), the 133 chain values and the 16 path digests,
  then `SigOk` of it (`true`). The chain starts are `Signer.chainStartF seed` (= the contract
  derivation `BLAKE2s-256 keyed by seed of (0x53 ‖ enc64 j ‖ i)`, `chainStartF_eq`); the tree is
  `Signer.buildTree` (= `Signer.node`, `buildTree_get`); the signature `Signer.Tree.sign`
  (= `Signer.sign`, `Tree.sign_eq`). Building the tree takes one pass over the 2^16 keys.
-/
import RecursionFast.Library.SignerFast

open RecursionFast

def hexDigit (c : Char) : Nat :=
  if c ≤ '9' then c.toNat - '0'.toNat else if c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else c.toNat - 'a'.toNat + 10

def unhex : List Char → List UInt8
  | a :: b :: r => (16 * hexDigit a + hexDigit b).toUInt8 :: unhex r
  | _ => []

def hexByte (b : UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.mk [d.getD (b.toNat / 16) '0', d.getD (b.toNat % 16) '0']

def hexDigest (d : Digest) : String := String.join (d.toList.map hexByte)

def toDigest (l : List UInt8) : Digest := Vector.ofFn fun i => l.getD i 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [seedHex, jStr, msgHex] =>
    let seed := unhex seedHex.toList
    let j := jStr.toNat!
    let m := toDigest (unhex msgHex.toList)
    if seed.length != 32 || j ≥ 2 ^ sigHeight then
      IO.eprintln "usage: signer <seed-hex (32 bytes)> <j < 65536> <message-hex (32 bytes)>"
      return 2
    let sk := Signer.chainStartF seed
    let T := Signer.buildTree sk
    let vk := Signer.Tree.pk T
    let σ := Signer.Tree.sign sk T j m
    IO.println (hexDigest vk)
    IO.println (toString σ.idx)
    for d in σ.ots do IO.println (hexDigest d)
    for d in σ.path do IO.println (hexDigest d)
    IO.println (toString (SigOkF vk m σ))
    return 0
  | _ =>
    IO.eprintln "usage: signer <seed-hex (32 bytes)> <j < 65536> <message-hex (32 bytes)>"
    return 2
