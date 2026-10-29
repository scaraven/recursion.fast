/-
  The compiled extractor interpreter on the library's witness-sending entry (an organiser test, run
  once per harness commit by the core CI; not trusted). V4-A9 removed the per-entry liveness check:
  the extractor's correctness is the kernel-checked `Computes` (`WitnessSending.computes`). This
  executable checks that Lean's compiled code for the contract's interpreter (`XProg.run`) agrees
  with it on that entry: on a leaf proof, on a node proof over two signed children (one with a
  trace entry) and on a proof one byte short, `ext` halts within the declared fuel with at most
  `outCap` words, and its output denotes exactly the extractor specification's result `E`; on a
  node proof cut short, that result is nothing.

    lake -f scripts/speed/lakefile.toml build extract && .lake/build/bin/extract [seed]
-/
import RecursionFast.Library.WitnessSending

open RecursionFast
open RecursionFast.WitnessSending (encodeF)

/-- The witness-sending submission. -/
def S : Submission := WitnessSending.submission

/-- The output of `ext` on the tape of `(c, π)` and the empty log, run by the compiled contract
interpreter within the submission's fuel. -/
def runExt (c : Digest) (π : Proof) : Option (List Word) :=
  let tape := extractorInput c π []
  S.ext.run tape (S.fuel tape.length)

/-- One case: `ext` halts within the fuel with at most `outCap` words denoting `E`'s result (the
same canonical encoding, or both nothing), and that result is a witness exactly when `some` is
expected. -/
def check (name : String) (c : Digest) (π : Proof) (wantSome : Bool) : IO Bool := do
  let e := S.E c π []
  match runExt c π with
  | none => IO.println s!"FAIL {name}: ext did not halt within the fuel"; pure false
  | some o =>
    let good := o.length ≤ outCap && (decodeWit o).map encodeF == e.map encodeF &&
      e.isSome == wantSome
    IO.println s!"{if good then "ok  " else "FAIL"} {name}: {π.size} B proof, {o.length} output words, {
      if e.isSome then "a witness" else "nothing"}"
    pure good

def main (args : List String) : IO UInt32 := do
  let seed := (args.headD "7").toNat!
  let dig (i : Nat) : Digest := Vector.ofFn fun j => (i * 37 + j.val + seed).toUInt8
  let sig (i : Nat) : Sig :=
    ⟨i, List.replicate wotsLen (dig (i + 1)), List.replicate sigHeight (dig (i + 2))⟩
  let p₁ : Signed := ⟨encodeF (.leaf (dig 2) 5), [], sig 3⟩
  let p₂ : Signed := ⟨encodeF (.leaf (dig 4) 6), [(⟨#[1, 2, 3]⟩, dig 5)], sig 6⟩
  let πl := encodeF (.leaf (dig 1) (1000 + seed))
  let πn := encodeF (.node (dig 7) (dig 8) p₁ p₂)
  let c := dig 9
  let rs ← [("leaf", πl, true), ("node over two signed children", πn, true),
    ("leaf proof one byte short", πl.extract 0 (πl.size - 1), true),
    ("node proof cut to 100 bytes", πn.extract 0 100, false)].mapM fun (n, π, w) => check n c π w
  let fails := rs.count false
  IO.println s!"{fails} failure(s)"
  return if fails = 0 then 0 else 1
