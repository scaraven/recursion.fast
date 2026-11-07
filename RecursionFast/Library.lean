/-
# recursion.fast (the signed random oracle): the organiser's untrusted, kernel-checked library.

Keccak (the general facts of the contract's hash) · Oracle (`OProg.run`, the result under an
oracle function) · Security (the knowledge state `KState`) · PaperTheorem (the bridge `KState.ks`)
· Completeness (`failProb`, perfect completeness) · Machine · Tree · Words (the extractor's output
format) · Prob (the calculus of the contract's `prob`) · KS (knowledge soundness against an
adversary that reads its log, the union bound) · Trace (`runSeq` to `runLog`, trace-encoding
injectivity) · Signer (the reference signer and `sigOk_sign`) · KeccakFast and Fast (the
word-level badge path, proved equal) · WitnessSending (certified for every key) · SigTrust (no
certified verifier trusts a signature) · Compose (the composition walk across the harness tree and
its probability) · SignerFast (the executable reference signer).
-/
import RecursionFast.Library.Keccak
import RecursionFast.Library.Oracle
import RecursionFast.Library.Security
import RecursionFast.Library.Prob
import RecursionFast.Library.KS
import RecursionFast.Library.PaperTheorem
import RecursionFast.Library.Completeness
import RecursionFast.Library.Machine
import RecursionFast.Library.Words
import RecursionFast.Library.Tree
import RecursionFast.Library.Trace
import RecursionFast.Library.Signer
import RecursionFast.Library.KeccakFast
import RecursionFast.Library.Fast
import RecursionFast.Library.WitnessSending
import RecursionFast.Library.SigTrust
import RecursionFast.Library.Compose
import RecursionFast.Library.SignerFast
