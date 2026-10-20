/-
# Exploration probes (UNTRUSTED; branch `explore/relativized-nark`)

Not part of the default targets: `lake build RecursionFastExplore`. Probe P1, the relativized
relation (`docs/explore/BRIEF.md`, notes in `docs/explore/notes/P1-lean-probes.md`):
* `Relativized/Defs`: `RelL`, `RelH`, `KStateRel`, `KSRel`, log monotonicity, abstract codecs.
* `Relativized/Compose`: whole-tree extraction from one log (`compose`, `compose_flat`), and v3's
  knowledge state does not compose (`V3.v3_no_compose`).
* `Relativized/Concat`: concatenation meets the relativized requirement with the leaf's potential
  (`concatState`); witness-sending has a relativized knowledge state at `0` (`ws_ksRel`).
* `Relativized/Backdoor`: the O-25 backdoor is relativized-sound (`Backdoor.backdoor`).
* `Relativized/Lazy`: a lazy parent is unsound (`lazy_no_kstate`, `lazy_extractor_collides`); a
  re-asking parent is sound (`deferState`).
-/
import RecursionFast.Explore.Relativized.Defs
import RecursionFast.Explore.Relativized.Compose
import RecursionFast.Explore.Relativized.Concat
import RecursionFast.Explore.Relativized.Backdoor
import RecursionFast.Explore.Relativized.Lazy
import RecursionFast.Explore.Attested.All
import RecursionFast.Explore.TwoChannel.Backdoor
import RecursionFast.Explore.Lift.All
