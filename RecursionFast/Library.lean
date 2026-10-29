/-
# recursion.fast v4 (SROM): the organiser's untrusted, kernel-checked library.

Ported from v3: Blake2s, Oracle (with `OProg.run`, which left the contract), Security (with
`KState`, which left the contract, V4-A10), PaperTheorem (the bridge `KState.ks`), Completeness
(with `failProb`), Machine, Tree, Words (the v4 output format). New in v4: Prob (the calculus of
the contract's `prob`), KS (knowledge soundness against an adversary that reads its log, the union
bound), Trace (`runSeq` to `runLog`, trace-encoding injectivity), Signer (the reference signer and
`sigOk_sign`), Blake2sFast and Fast (the word-level badge path, proved equal), WitnessSending
(certified for every key), SigTrust (no certified verifier trusts a signature), Compose (the
composition walk across the harness tree and its probability, V4-8), SignerFast (the executable
reference signer).
-/
import RecursionFast.Library.Blake2s
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
import RecursionFast.Library.Blake2sFast
import RecursionFast.Library.Fast
import RecursionFast.Library.WitnessSending
import RecursionFast.Library.SigTrust
import RecursionFast.Library.Compose
import RecursionFast.Library.SignerFast
