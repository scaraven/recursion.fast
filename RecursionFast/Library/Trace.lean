/-
  RecursionFast.Library.Trace  (UNTRUSTED, kernel-checked)

  Facts about running a program on a trace (`OProg.runSeq`, V4-4, V4-A3) and about the trace
  digest (`Contract/Signature.lean`).

  * **The bridge to the log** (`runLog_of_runSeq`): if a program accepts on a trace, every entry
    of the trace is in the log `L`, and `L` is functional (no query with two answers), then the
    program returns the same on `L`. This is the step of the composition argument (V4-8,
    `Library/Compose.lean`) from "the signed trace is genuine" to the knowledge state's `final`
    law, which reads the verifier from the log.
  * `runSeq_queries`: the trace of a program's own run under an oracle `H` (its queries with `H`'s
    answers) answers the run: the honest trace the service signs.
  * `runSeq_ret`, `runSeq_ret_cons`: exact consumption, a returned program accepts only the empty
    trace. `runSeq_map_fst`, `runSeq_length_le`: an accepted trace consistent with an oracle is
    the program's query sequence under it, so a functional accepted trace has at most `qV`
    entries (V4-A3's "the signed trace is the verifier's query sequence").
  * **Injectivity of the trace digest's encoding** (`traceBytes_inj`): two traces whose queries
    are shorter than `2^64` bytes (so every trace `acc` accepts, `queryCap`) with the same bytes
    are equal. So equal digests of two different accepted traces are a BLAKE2s collision
    (`traceDigest_eq`), which `Collision` records as data.
-/
import RecursionFast.Library.Words
import RecursionFast.Library.Oracle

namespace RecursionFast

/-- A BLAKE2s-256 collision: two different byte strings with one digest. -/
structure Collision where
  /-- The first byte string. -/
  x : List UInt8
  /-- The second byte string. -/
  y : List UInt8
  /-- They differ. -/
  ne : x ≠ y
  /-- Their digests are equal. -/
  eq : blake2sDigest x = blake2sDigest y

/-- A log is functional: no query has two answers in it (true of every log of an oracle). -/
def Log.Functional (L : Log) : Prop := ∀ e ∈ L, ∀ e' ∈ L, e.1 = e'.1 → e.2 = e'.2

namespace OProg
variable {α : Type}

theorem runSeq_ret (a : α) : (OProg.ret a).runSeq [] = some a := rfl

/-- **Exact consumption**: a program that has returned rejects every non-empty trace. -/
theorem runSeq_ret_cons (a : α) (e : ByteArray × Digest) (tr : Trace) :
    (OProg.ret a).runSeq (e :: tr) = none := rfl

theorem runSeq_query (q : ByteArray) (k : Digest → OProg α) (a : Digest) (tr : Trace) :
    (OProg.query q k).runSeq ((q, a) :: tr) = (k a).runSeq tr := by
  simp [runSeq]

/-- **The bridge to the log**: a verdict on a trace whose entries are all in a functional log is
the verdict on the log. -/
theorem runLog_of_runSeq {L : Log} (hL : L.Functional) :
    ∀ (p : OProg α) (tr : Trace) {b : α}, p.runSeq tr = some b → (∀ e ∈ tr, e ∈ L) →
      p.runLog L = some b
  | .ret a, [], b, h, _ => h
  | .ret _, _ :: _, _, h, _ => nomatch h
  | .query _ _, [], _, h, _ => nomatch h
  | .query q k, (q', a) :: tr, b, h, hin => by
    simp only [runSeq] at h
    split at h
    · rename_i hq
      subst hq
      have hmem : (q', a) ∈ L := hin _ (List.mem_cons_self ..)
      obtain ⟨e, he⟩ : ∃ e, L.find? (fun e => decide (e.1 = q')) = some e := by
        cases hf : L.find? (fun e => decide (e.1 = q')) with
        | none => exact absurd (List.find?_eq_none.mp hf _ hmem) (by simp)
        | some e => exact ⟨e, rfl⟩
      have h1 : e.1 = q' := by simpa using List.find?_some he
      have h2 : e.2 = a := hL e (List.mem_of_find?_eq_some he) _ hmem h1
      simp only [runLog, he, Option.bind_some, h2]
      exact runLog_of_runSeq hL (k a) tr h fun e he => hin e (List.mem_cons_of_mem _ he)
    · cases h

/-- **The honest trace**: a program's own queries under `H`, with `H`'s answers, answer it. -/
theorem runSeq_queries (H : ByteArray → Digest) :
    ∀ p : OProg α, p.runSeq ((p.queries H).map fun q => (q, H q)) = some (p.run H)
  | .ret _ => rfl
  | .query q k => by
    simp only [queries, List.map_cons, runSeq, ite_true, run]
    exact runSeq_queries H (k (H q))

/-- **On a trace consistent with an oracle `H`, the trace is the program's queries under `H`.** -/
theorem runSeq_map_fst (H : ByteArray → Digest) :
    ∀ (p : OProg α) (tr : Trace) {b : α}, p.runSeq tr = some b → (∀ e ∈ tr, H e.1 = e.2) →
      tr.map Prod.fst = p.queries H
  | .ret _, [], _, _, _ => rfl
  | .ret _, _ :: _, _, h, _ => nomatch h
  | .query _ _, [], _, h, _ => nomatch h
  | .query q k, (q', a) :: tr, b, h, hH => by
    simp only [runSeq] at h
    split at h
    · rename_i hq
      subst hq
      have ha : H q' = a := hH _ (List.mem_cons_self ..)
      simp only [List.map_cons, queries, ha]
      rw [runSeq_map_fst H (k a) tr h fun e he => hH e (List.mem_cons_of_mem _ he)]
    · cases h

/-- **An accepted functional trace is at most `qV` long** when the program asks at most `qV`
queries under every oracle (the query bound of `KS`): it is the program's query sequence under an
oracle that agrees with it. (A trace with two answers to one query lies on no oracle's path; a
signed trace is functional, the service being a function.) -/
theorem runSeq_length_le {p : OProg α} {tr : Trace} {b : α} {qV : ℕ} (h : p.runSeq tr = some b)
    (hf : Log.Functional tr) (hq : ∀ H, (p.queries H).length ≤ qV) : tr.length ≤ qV := by
  let H : ByteArray → Digest := fun q =>
    ((tr.find? fun e => e.1 = q).map Prod.snd).getD (Vector.replicate 32 0)
  have hH : ∀ e ∈ tr, H e.1 = e.2 := by
    intro e he
    obtain ⟨e', he'⟩ : ∃ e', tr.find? (fun x => decide (x.1 = e.1)) = some e' := by
      cases hfd : tr.find? (fun x => decide (x.1 = e.1)) with
      | none => exact absurd (List.find?_eq_none.mp hfd e he) (by simp)
      | some e' => exact ⟨e', rfl⟩
    have h1 : e'.1 = e.1 := by simpa using List.find?_some he'
    simp only [H, he', Option.map_some, Option.getD_some]
    exact hf e' (List.mem_of_find?_eq_some he') e he h1
  have := congrArg List.length (runSeq_map_fst H p tr h hH)
  rw [List.length_map] at this
  exact this ▸ hq H

end OProg

/-! ## The trace digest -/

theorem traceBytes_nil : traceBytes [] = [] := rfl

theorem traceBytes_cons (e : ByteArray × Digest) (tr : Trace) :
    traceBytes (e :: tr) = enc64 e.1.size ++ e.1.data.toList ++ e.2.toList ++ traceBytes tr := by
  simp [traceBytes]

/-- **The trace encoding is injective** on traces whose queries are shorter than `2^64` bytes. -/
theorem traceBytes_inj : ∀ {tr tr' : Trace}, (∀ e ∈ tr, e.1.size < 2 ^ 64) →
    (∀ e ∈ tr', e.1.size < 2 ^ 64) → traceBytes tr = traceBytes tr' → tr = tr'
  | [], [], _, _, _ => rfl
  | [], e :: tr', _, _, h => by
    have := congrArg List.length h
    simp [traceBytes_cons, traceBytes_nil, enc64_length] at this; omega
  | e :: tr, [], _, _, h => by
    have := congrArg List.length h
    simp [traceBytes_cons, traceBytes_nil, enc64_length] at this
  | (q, a) :: tr, (q', a') :: tr', h, h', heq => by
    simp only [traceBytes_cons, List.append_assoc] at heq
    obtain ⟨h1, heq⟩ := List.append_inj heq (by simp [enc64_length])
    have hs : q.size = q'.size := enc64_inj (h _ (List.mem_cons_self ..))
      (h' _ (List.mem_cons_self ..)) h1
    obtain ⟨h2, heq⟩ := List.append_inj heq (by simpa using hs)
    obtain ⟨h3, heq⟩ := List.append_inj heq (by simp)
    have hq : q = q' := ByteArray.ext (Array.ext' h2)
    have ha : a = a' := Vector.toList_inj.mp h3
    rw [hq, ha, traceBytes_inj (fun e he => h e (List.mem_cons_of_mem _ he))
      (fun e he => h' e (List.mem_cons_of_mem _ he)) heq]

/-- Equal digests of different strings are a collision. -/
def Collision.of {x y : List UInt8} (hne : x ≠ y) (heq : blake2sDigest x = blake2sDigest y) :
    Collision := ⟨x, y, hne, heq⟩

/-- **Equal trace digests**: the traces are equal, or their bytes collide. -/
theorem traceDigest_eq {tr tr' : Trace} (h : ∀ e ∈ tr, e.1.size < 2 ^ 64)
    (h' : ∀ e ∈ tr', e.1.size < 2 ^ 64) (heq : traceDigest tr = traceDigest tr') :
    tr = tr' ∨ ∃ c : Collision, c.x = tagTrace :: traceBytes tr ∧
      c.y = tagTrace :: traceBytes tr' := by
  by_cases ht : tr = tr'
  · exact Or.inl ht
  · refine Or.inr ⟨⟨_, _, fun hb => ht (traceBytes_inj h h' (List.cons.inj hb).2), heq⟩, rfl, rfl⟩

end RecursionFast
