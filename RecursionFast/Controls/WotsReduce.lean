/-
# Controls: the reduction of EUF-CMA to a collision or a chain inversion (`Library/WotsReduce.lean`)

Positive (the inversion outcome is reached, for every secret function `sk`, symbolically: no hash
is evaluated). The forger that knows `sk` signs a fresh message `m` with the reference signer:
* at an unused index (`reduce_unused`: the record is empty) and at an index the record used for
  another message (`reduce_used`: key `0` signed `0x00…00`, the forger signs `0xFF…FF` with it),
  `wotsReduce` returns an inversion;
* at the used index, the chain the reduction compares is computed (`pick_used`, `decide
  +kernel`): chain `131`, the first whose digit of `0xFF…FF` (`3` on the 128 message chains, `0`
  on the checksum chains) is below the digit of `0x00…00` (`0` on the message chains,
  `0, 0, 0, 2, 1` on the checksum chains), so the forger's value there is the honest value at
  position `0`, below the revealed position `2`;
* a replayed record (`[(0, 0x00…00), (0, 0x00…00)]`, the service re-issuing one signature) has one
  message per index (`oneMsg_replay`), and the forgery reduces to an inversion against it as well
  (`reduce_replay`).
Positive, through the composition walks (with `queryLeaf` of `Controls/Compose.lean`, the leaf
proof of the one-entry trace `(qMax, a)` signed with `sign sk 0` on its digest, and a service
that signed nothing): the stream walk's and the tree walk's EUF-CMA forgery reduces to a chain
inversion (`walkStreamSigned_queryLeaf_inversion`, `walkSigned_queryLeaf_inversion`), so the
adversary that holds the key, asks nothing and outputs that proof makes the chain-inversion term
of `compose_prob_stream_wots` (and of `compose_prob_wots`) certain (`queryLeaf_inversion_prob`,
`queryLeaf_inversion_prob_tree`).

Negative (the inversion outcome is not satisfiable by revealed values).
* `not_inversion_of_revealed`: against a record holding `(σ.idx, m₀)`, a forgery on a message
  whose every digit is at least `m₀`'s (whose chain values are all computable forward from the
  issued signature) has no inversion outcome: every `WotsBreak` of it is a collision. By
  `wotsDigits_dominates` such a message is `m₀` itself (`not_inversion_issued`), which
  `wotsReduce` never sees (its forgeries are on fresh messages): the control is on the type, that
  `unrevealed` excludes every position the signer revealed. That a revealed value placed in a
  forgery on a fresh message fails `value` is no kernel fact: it needs the hash.
* `not_inversion_twice`: one index used for two messages (`0x00…00` and `0xFF…FF`) reveals every
  position of every chain of the key (one of their digits is `0` on every chain), so no forgery
  with that index has an inversion outcome: the reduction needs one message per index, which that
  record violates (`not_oneMsg_twice`).

The hypotheses of `compose_prob_stream_wots` on a non-empty transcript (`transcript_honest_one`):
an honestly signed trace whose entries are in the log meets both `Transcript` and `Honest`; and
`accounted_transcript`: `accounted T L` of a transcript meets both, for every log. Negative
(`transcript_nil_any`): the empty transcript meets both for every run, so that `T` is the
service's **complete** transcript is not a hypothesis of the theorem: it stays on paper.

Negative (what the type does not say). `wotsBreak_nonempty`: `WotsBreak sk R m σ` is inhabited for
every forgery, by a pigeonhole collision (`Controls/Compose.lean`, `collision_nonempty`), so the
collision branch's content is the compiled `wotsReduce`. `no_self_collision`: the `collision`
branch cannot be filled with a string and itself (the field `Collision.ne`, stated as the
impossibility it gives).
-/
import RecursionFast.Library.WotsReduce
import RecursionFast.Controls.Signature
import RecursionFast.Controls.Compose

namespace RecursionFast.Controls.WotsReduce
open RecursionFast RecursionFast.Signer RecursionFast.WotsReduce

variable (sk : ℕ → ℕ → Digest)

/-- The all-`0x00` message. -/
def m0 : Digest := Vector.replicate 32 0

/-- The all-`0xFF` message. -/
def mF : Digest := Vector.replicate 32 0xFF

/-! ## Positive: a forger that knows the key is reduced to an inversion -/

/-- At an unused index (the record is empty), the honest signature of a fresh message reduces to
an inversion. -/
theorem reduce_unused (m : Digest) :
    (wotsReduce sk [] (fun _ ha => absurd ha List.not_mem_nil) m (sign sk 0 m)
      (sigOk_sign sk 0 (by decide) m) (fun _ hx => absurd hx List.not_mem_nil)).IsInversion :=
  wotsReduce_sign sk [] _ (by decide) m _

theorem mF_ne_m0 : mF ≠ m0 := by decide

/-- A record of one entry has one message per index. -/
theorem oneMsg_single (x : ℕ × Digest) : OneMsg [x] := fun _ ha _ hb _ => by
  rw [List.mem_singleton.mp ha, List.mem_singleton.mp hb]

/-- **A replay keeps one message per index**: the service re-issuing one signature repeats the
index with the same message. -/
theorem oneMsg_replay : OneMsg [(0, m0), (0, m0)] := fun a ha b hb _ => by
  rw [List.mem_pair.mp ha |>.elim id id, List.mem_pair.mp hb |>.elim id id]

/-- One index with two messages is not one message per index. -/
theorem not_oneMsg_twice : ¬ OneMsg [(0, m0), (0, mF)] := fun h =>
  mF_ne_m0 (h (0, mF) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (0, m0)
    List.mem_cons_self rfl)

/-- At an index the record used for `0x00…00`, the honest signature of `0xFF…FF` with it reduces
to an inversion. -/
theorem reduce_used :
    (wotsReduce sk [(0, m0)] (oneMsg_single _) mF (sign sk 0 mF)
      (sigOk_sign sk 0 (by decide) mF) (by simpa using mF_ne_m0.symm)).IsInversion :=
  wotsReduce_sign sk _ _ (by decide) mF _

/-- Against the replayed record, the honest signature of `0xFF…FF` with key `0` reduces to an
inversion too. -/
theorem reduce_replay :
    (wotsReduce sk [(0, m0), (0, m0)] oneMsg_replay mF (sign sk 0 mF)
      (sigOk_sign sk 0 (by decide) mF) (by simpa using mF_ne_m0.symm)).IsInversion :=
  wotsReduce_sign sk _ _ (by decide) mF _

/-- The chain compared at the used index: chain `131`, the first whose digit of the forged
`0xFF…FF` is below the signed `0x00…00`'s (`0 < 2`). -/
theorem pick_used :
    (pick [(0, m0)] (oneMsg_single _) 0 mF (by simpa using mF_ne_m0.symm)).val = 131 := by
  decide +kernel

/-! ## Negative: revealed values are no inversion -/

/-- **A forgery computed forward from an issued signature is no inversion**: if the record holds
`(σ.idx, m₀)` and every digit of `m` is at least `m₀`'s, every outcome is a collision. -/
theorem not_inversion_of_revealed {R : List (ℕ × Digest)} {m m₀ : Digest} {σ : Sig}
    (hmem : (σ.idx, m₀) ∈ R) (hle : ∀ i, (wotsDigits m₀).getD i 0 ≤ (wotsDigits m).getD i 0)
    (b : WotsBreak sk R m σ) : b.IsCollision := by
  cases b with
  | collision => trivial
  | inversion i _ _ _ hu => exact absurd (hu m₀ hmem) (Nat.not_lt.mpr (hle i))

/-- **The issued signature is no inversion**: a forgery on a message the record signed with its
index has only collision outcomes. -/
theorem not_inversion_issued {R : List (ℕ × Digest)} {m : Digest} {σ : Sig}
    (hmem : (σ.idx, m) ∈ R) (b : WotsBreak sk R m σ) : b.IsCollision :=
  not_inversion_of_revealed sk hmem (fun _ => le_rfl) b

/-- One of the digits of `0x00…00` and `0xFF…FF` is `0` on every chain. -/
theorem digits_m0_mF (i : ℕ) : (wotsDigits m0).getD i 0 = 0 ∨ (wotsDigits mF).getD i 0 = 0 := by
  rw [m0, mF, Controls.Signature.wotsDigits_zero, Controls.Signature.wotsDigits_ff]
  by_cases hi : i < 133
  · have : ∀ i < 133, (List.replicate 128 0 ++ [0, 0, 0, 2, 1]).getD i 0 = 0 ∨
        (List.replicate 128 3 ++ [0, 0, 0, 0, 0]).getD i 0 = 0 := by decide
    exact this i hi
  · left
    rw [List.getD_eq_default]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega

/-- **One index, two messages: no inversion.** If key `σ.idx` signed both `0x00…00` and
`0xFF…FF` (a record `OneMsg` excludes, `not_oneMsg_twice`), every position of every chain is
revealed, and every outcome is a collision. -/
theorem not_inversion_twice {m : Digest} {σ : Sig}
    (b : WotsBreak sk [(σ.idx, m0), (σ.idx, mF)] m σ) : b.IsCollision := by
  cases b with
  | collision => trivial
  | inversion i _ _ _ hu =>
    rcases digits_m0_mF i with h | h
    · exact absurd (hu m0 (by simp)) (by rw [h]; omega)
    · exact absurd (hu mF (by simp)) (by rw [h]; omega)

/-! ## Negative: what the type does not say -/

/-- **The type is inhabited for every forgery**, by a pigeonhole collision: the collision
branch's content is the compiled `wotsReduce`. -/
theorem wotsBreak_nonempty (R : List (ℕ × Digest)) (m : Digest) (σ : Sig) :
    Nonempty (WotsBreak sk R m σ) :=
  Controls.Compose.collision_nonempty.map .collision

/-- **No byte string collides with itself**: the `collision` branch needs two different
preimages. -/
theorem no_self_collision (x : List UInt8) : ¬ ∃ c : Collision, c.x = x ∧ c.y = x :=
  fun ⟨c, hx, hy⟩ => c.ne (hx.trans hy.symm)

/-! ## Positive: the chain-inversion term of the composition theorems is reached -/

open RecursionFast.Compose
open RecursionFast.Controls.Compose (queryLeaf acc_queryLeaf)
open RecursionFast.Controls.Relation (oneQuery qMax)

/-- The empty transcript (a service that signed nothing). -/
theorem transcript_nil : Transcript sk [] := ⟨nofun, nofun⟩

/-- **Through the stream walk**: on the one-leaf stream, with the empty log and a service that
signed nothing, the walk's EUF-CMA forgery (`queryLeaf`, signed with key `0`) reduces to a chain
inversion. -/
theorem walkStreamSigned_queryLeaf_inversion (xs : List Digest) (a : Digest)
    (hn : xs.length ≤ leafCap) :
    (walkStreamSigned [] [] ⟨nofun, nofun⟩ xs.length hn [dataRoot xs] (queryLeaf sk xs a)
      (acc_queryLeaf sk xs a hn)).IsWotsInversion (transcript_nil sk) :=
  have hacc := acc_queryLeaf sk xs a hn
  Outcome.isWotsInversion_reduce_forgery _ _
    ⟨queryLeaf sk xs a, (acc_parts hacc).2.1, (acc_parts hacc).2.2.1,
      fun h => List.not_mem_nil (h _ (List.mem_singleton_self _))⟩ _ _ _ nofun (by decide) rfl

/-- **The chain-inversion term of `compose_prob_stream_wots` is reached**: against a service that
signed nothing, the adversary that holds the key, asks nothing and outputs `queryLeaf` makes it
certain. -/
theorem queryLeaf_inversion_prob (xs : List Digest) (a : Digest) (hn : xs.length ≤ leafCap) :
    prob (fun p L => ∃ hacc : (oneQuery qMax).acc (pk sk)
        (streamStmt xs.length [dataRoot xs]) p = true,
      (walkStreamSigned L [] ⟨nofun, nofun⟩ xs.length hn [dataRoot xs] p hacc).IsWotsInversion
        (transcript_nil sk)) (.ret (queryLeaf sk xs a)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, walkStreamSigned_queryLeaf_inversion sk xs a hn⟩)

/-- **Through the tree walk**: the same on the one-leaf tree. -/
theorem walkSigned_queryLeaf_inversion (xs : List Digest) (a : Digest)
    (hn : xs.length ≤ leafCap) :
    (walkSigned [] [] ⟨nofun, nofun⟩ xs.length hn 0 [dataRoot xs] rfl (queryLeaf sk xs a)
      (acc_queryLeaf sk xs a hn)).IsWotsInversion (transcript_nil sk) := by
  unfold walkSigned walk walkFrom
  rw [extract_forgery (L := []) _ fun h => List.not_mem_nil (h _ (List.mem_singleton_self _))]
  exact Outcome.isWotsInversion_reduce_forgery _ _ _ _ _ _ nofun (by decide) rfl

/-- **The chain-inversion term of `compose_prob_wots` is reached**, likewise. -/
theorem queryLeaf_inversion_prob_tree (xs : List Digest) (a : Digest)
    (hn : xs.length ≤ leafCap) :
    prob (fun p L => ∃ hacc : (oneQuery qMax).acc (pk sk)
        (treeRoot ([dataRoot xs].map fun h => leafStmt h xs.length)) p = true,
      (walkSigned L [] ⟨nofun, nofun⟩ xs.length hn 0 [dataRoot xs] rfl p hacc).IsWotsInversion
        (transcript_nil sk)) (.ret (queryLeaf sk xs a)) [] = 1 :=
  (prob_ret _ _ _).trans (ind_of ⟨_, walkSigned_queryLeaf_inversion sk xs a hn⟩)

/-! ## The transcript hypotheses -/

/-- **A non-empty honest transcript**: one trace, signed by the reference signer at index `0`,
whose entries are the log's, meets both `Transcript` and `Honest`. -/
theorem transcript_honest_one (tr : Trace) (hcap : ∀ e ∈ tr, e.1.size ≤ queryCap) :
    Transcript sk [(tr, sign sk 0 (traceDigest tr))] ∧
      Honest [(tr, sign sk 0 (traceDigest tr))] tr := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro x hx; rw [List.mem_singleton.mp hx]; rfl
  · intro x hx y hy _; rw [List.mem_singleton.mp hx, List.mem_singleton.mp hy]
  · intro x hx e he; rw [List.mem_singleton.mp hx] at he; exact he
  · intro x hx e he; rw [List.mem_singleton.mp hx] at he; exact hcap e he

/-- **`accounted` meets both hypotheses**, for every transcript and log. -/
theorem accounted_transcript {T : List (Trace × Sig)} (hS : Transcript sk T) (L : Log) :
    Transcript sk (accounted T L) ∧ Honest (accounted T L) L :=
  ⟨hS.accounted sk L, honest_accounted T L⟩

/-- **Completeness of the transcript is not a hypothesis**: the empty transcript meets both
`Transcript` and `Honest` for every run. -/
theorem transcript_nil_any (L : Log) :
    Transcript sk ([] : List (Trace × Sig)) ∧ Honest ([] : List (Trace × Sig)) L :=
  ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩

end RecursionFast.Controls.WotsReduce
