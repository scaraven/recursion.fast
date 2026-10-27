/-
# recursion.fast v4 (SROM): the trusted contract, in reading order (docs/v4/BRIEF.md §4).

Hash.Blake2s (v2, unchanged) · Relation (signed children, V4-16) · Signature (trace digest and
WOTS/Merkle check, V4-3) · Oracle (adds `runSeq`, V4-4) · Security (`prob` and the textbook
single-output `KS`, V4-A10; completeness v3's, caps V4-A9) · Machine (v3, unchanged) · Extractor
(output format for signed children, V4-6) · Tree (v3, unchanged) · Certificate (`vk`, `acc`,
every key, V4-1, V4-7). No field anywhere (V3-1). The contract imports Lean core and Mathlib
only.
-/
import RecursionFast.Contract.Hash.Blake2s
import RecursionFast.Contract.Relation
import RecursionFast.Contract.Signature
import RecursionFast.Contract.Oracle
import RecursionFast.Contract.Security
import RecursionFast.Contract.Machine
import RecursionFast.Contract.Extractor
import RecursionFast.Contract.Tree
import RecursionFast.Contract.Certificate
