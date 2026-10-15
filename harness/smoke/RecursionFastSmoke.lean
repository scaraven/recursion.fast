/-
# Smoke-test "submission" for the badge path: NOT SECURE, NOT A SUBMISSION         (Stage 6b)

The badge path (DESIGN §7.4 step 3: build `verify` and `index`, index, run the benchmark) cannot
be exercised on a secure protocol in this repository: the only secure ones send the witness, whose
oracles of `2^(k+8)` … `2^(k+10)` elements no executable can index or prove (O-10). So the
harness's plumbing and timing tests run on the compile control `cmpToy : Protocol 20`
(`Controls/CompileToy.lean`): a 4-leaf committed oracle, one challenge round, one plain element,
a 2-leaf index oracle. **It is not secure** (its verifier ignores the layout and the statement
except `x 0`) and **this is not a `Submission`**: `SmokeSubmission` has no `secure` field. It has
exactly the two fields the badge executables read, `P` and `cfg`, so the production template
`harness/lean/Main.lean.in` builds `verify` and `index` from it unchanged.

* `submission`: `cmpToy` at arity 2. Its key does not depend on the layout (`cmpVK`, `cmpIDX` are
  constant), so every layout has the key `vkc2` of `Controls/CompileToy.lean`.
* `keyed`: `cmpToy` with a key that depends on the layout (its one element is the xor of the
  layout's serialisation `Layout.words`), for the harness's key-digest controls (S5-A13: a claim
  whose `digestL` is that of `L_chain(16)` instead of `L_chain(2^10)` must be rejected; with
  `submission` the two digests coincide).
-/
import RecursionFast.Controls.CompileToy

namespace RecursionFastSmoke
open RecursionFast RecursionFast.Controls.Compile

/-- NOT a `Submission` (no security proof): a protocol and its configuration, the two fields the
badge executables read. -/
structure SmokeSubmission (k : ℕ) where
  /-- The protocol (NOT SECURE). -/
  P : Protocol k
  /-- The compilation configuration. -/
  cfg : Cfg

/-- **The smoke-test protocol**: the compile control `cmpToy` at arity 2. NOT SECURE. -/
def submission : SmokeSubmission 20 := ⟨cmpToy, cfg2⟩

/-- A key element depending on the whole layout: the xor of its serialisation. -/
def layoutKey (L : Layout K) : Fin 1 → K :=
  fun _ => ⟨(Layout.words L).foldl (· ^^^ ·) 0x1234⟩

/-- `cmpToy` with the layout-dependent key `layoutKey` (for the digest controls). NOT SECURE. -/
def keyed : SmokeSubmission 20 := ⟨{ cmpToy with VK := layoutKey }, cfg2⟩

end RecursionFastSmoke
