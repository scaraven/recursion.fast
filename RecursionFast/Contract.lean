/-
# recursion.fast (the signed random oracle): the trusted contract, in reading order.

Hash.Keccak (Ethereum's Keccak-256) · Relation (leaf and node statements, signed children) ·
Signature (trace digest and WOTS/Merkle check) · Oracle (query programs, `runSeq`) · Security
(`prob`, the textbook single-output `KS`, completeness with error, the caps) · Machine (the
extractor's machine) · Extractor (output format for signed children, its domain) · Tree (the root
of `2^r` leaves) · Certificate (`vk`, `acc`, every key; no proof cap). No field anywhere.
The contract imports Lean core and Mathlib only.
-/
import RecursionFast.Contract.Hash.Keccak
import RecursionFast.Contract.Relation
import RecursionFast.Contract.Signature
import RecursionFast.Contract.Oracle
import RecursionFast.Contract.Security
import RecursionFast.Contract.Machine
import RecursionFast.Contract.Extractor
import RecursionFast.Contract.Tree
import RecursionFast.Contract.Certificate
