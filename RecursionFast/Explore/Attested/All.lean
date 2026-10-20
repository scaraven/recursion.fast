/-
# Exploration probe P2: the attested oracle (D4)                                   (UNTRUSTED)

Notes: `docs/explore/notes/P2-attested-lean.md`. Design: `docs/explore/notes/W2-attested-oracle.md`
§A.
* `Model`: items, events, the list encoding and its injectivity on bounded lists, `AProg` with
  `attest`, `runLog`/`runItems`/`calls`, `Valid`, `WF`, the lifting lemma `runItems_valid`, the
  embedding of the contract's programs.
* `KState`: `RelA`, `Out`, `IsColl`, `Sound`, `KStateA` (with the `cert` law), `KSA`; `WF` in
  `final` costs nothing; P1's relativized states lift (`KStateA.ofRel`).
* `Compose`: whole-tree extraction from one log, or a returned collision (`compose`,
  `compose_all`).
* `Escape`: the attesting node verifier, sound with one call per node (`attState`, `calls_node`,
  `att_W1`), and complete at a node (`attV_complete`).
* `Paper`: the paper theorem with certification moves (`Paper.paper`, `Paper.paper_tree`).
* `Controls`: the collision disjunct (`acceptAll_iff`, `acceptAll_choice`), `Valid`/`WF`
  negatives and positives, witness-sending, a depth-2 tree, the unbounded encoding.
-/
import RecursionFast.Explore.Attested.Model
import RecursionFast.Explore.Attested.KState
import RecursionFast.Explore.Attested.Compose
import RecursionFast.Explore.Attested.Escape
import RecursionFast.Explore.Attested.Paper
import RecursionFast.Explore.Attested.Controls
