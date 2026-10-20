/-
# Exploration: the attested oracle (D4), the model                                 (UNTRUSTED)

Branch `explore/relativized-nark`, probe P2 (`docs/explore/notes/W2-attested-oracle.md` §A.1–A.2,
notes in `docs/explore/notes/P2-attested-lean.md`). The harness's oracle service answers three
calls: `query q` (a random answer), `certify xs` (check that every item of the list `xs` is true of
the log so far, then record it), and `attest h` (is `h` the hash of a recorded list?). This file
models it.

* `Item` (`ans q a`: an oracle answer; `att h`: a hash of an earlier certified list) and `Ev`
  (the service's log events: `ans q a`, a fresh answer; `cert xs`, an accepted certification).
  `ALog := List Ev`.
* **The list encoding** (W2 §A.1, byte for byte): `ans q a ↦ 0x00 ‖ enc64 |q| ‖ q ‖ a`,
  `att h ↦ 0x01 ‖ h`, `encList` their concatenation, `hashList xs = BLAKE2s(tagList ‖ encList xs)`
  with `tagList = 0x41`. The item codes are prefix-free (`Item.enc_append_inj`), so `encList` is
  injective on **bounded** lists, whose queries are shorter than `2^64` bytes (`encList_inj`;
  `enc64` wraps at `2^64`, so it is not injective on all lists, W2 M1). `hashList_coll` turns two
  distinct bounded lists with one `hashList` into two distinct BLAKE2s preimages with one digest.
* `AProg`: query programs with `query` and `attest` (W2's `certify` constructor is left out; see
  the note). `runLog L` answers `query q` with the first `ans q _` event of `L` (`firstAns`) and
  `attest h` with `true` iff some `cert xs` of `L` has `hashList xs = h` (`attested`, `certOf`).
  `runItems xs` reads a program against a list of items, the in-circuit semantics of a child run:
  `query q` from the first `ans q _` item, `attest h` accepted only if `att h` is an item. `calls`
  lists the oracle calls of a run under an oracle function `H` and an attest predicate `A`.
* `Valid L xs`: every `ans` item is bounded and is `L`'s first answer to its query; every `att`
  item's hash is attested in `L`. `WF L`: every `cert xs` of `L` is `Valid` on the prefix before it.
  `WF` is kept by fresh answers and valid certifications (`WF.snoc_ans`, `WF.snoc_cert`), and a
  well-formed log's certified lists are valid on the whole log (`WF.valid_of_mem`).
* **The lifting lemma** `runItems_valid`: a verdict read from a list valid on `L` is the verdict
  read from `L`. This is what makes attestation sound.
* **The embedding of v3's model**: `OProg.toA` (a contract query program as an attested one) and
  `ansLog` (the contract log of a log's answers); `toA_runLog`: a lifted program reads the same
  verdict from `L` as the original from `ansLog L`.
-/
import RecursionFast.Explore.Relativized.Defs

namespace RecursionFast.Explore.Attested

open Relativized

/-! ## Items, events, logs -/

/-- Domain tag of a certified list's preimage: a fifth first byte, distinct from `tagChain`,
`tagLeaf`, `tagNode` and `tagRO`. -/
def tagList : UInt8 := 0x41

/-- An item of a certified list: an oracle answer `a` to the query `q`, or the hash `h` of an
earlier attested list. -/
inductive Item where
  /-- The oracle answered `a` to `q`. -/
  | ans (q : ByteArray) (a : Digest)
  /-- `h` is the hash of an attested list. -/
  | att (h : Digest)
  deriving DecidableEq

/-- An event of the service's log: a fresh oracle answer, or an accepted certification of a list. -/
inductive Ev where
  /-- The oracle answered `a` to the fresh query `q`. -/
  | ans (q : ByteArray) (a : Digest)
  /-- The service accepted the list `xs` and recorded its hash. -/
  | cert (xs : List Item)

/-- A log of the attested oracle: its events, in order. -/
abbrev ALog := List Ev

/-! ## The list encoding -/

/-- The bytes of an item: `0x00 ‖ enc64 |q| ‖ q ‖ a` for an answer, `0x01 ‖ h` for a hash. -/
def Item.enc : Item → List UInt8
  | .ans q a => 0x00 :: (enc64 q.size ++ q.data.toList ++ a.toList)
  | .att h => 0x01 :: h.toList

/-- The bytes of a list of items: the items' bytes, concatenated. -/
def encList (xs : List Item) : List UInt8 := xs.flatMap Item.enc

/-- **The hash of a list of items**: BLAKE2s-256 of `tagList ‖ encList xs`. -/
def hashList (xs : List Item) : Digest := blake2sDigest (tagList :: encList xs)

/-- An item is small when its query, if any, is shorter than `2^64` bytes (the range where `enc64`
is injective). -/
def Item.small : Item → Bool
  | .ans q _ => decide (q.size < 2 ^ 64)
  | .att _ => true

/-- A list is bounded when all its items are small. -/
def Bounded (xs : List Item) : Prop := ∀ x ∈ xs, x.small = true

instance (xs : List Item) : Decidable (Bounded xs) :=
  inferInstanceAs (Decidable (∀ x ∈ xs, x.small = true))

@[simp] theorem encList_nil : encList [] = [] := rfl

@[simp] theorem encList_cons (x : Item) (xs : List Item) :
    encList (x :: xs) = x.enc ++ encList xs := List.flatMap_cons

theorem Bounded.tail {x : Item} {xs : List Item} (h : Bounded (x :: xs)) : Bounded xs :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- `enc64` is injective below `2^64`. -/
theorem enc64_inj {n m : ℕ} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (h : enc64 n = enc64 m) :
    n = m := by
  have hd : ∀ i : Fin 8, n / 256 ^ i.val % 256 = m / 256 ^ i.val % 256 := fun i => by
    have := congrArg UInt8.toNat (congrFun (List.ofFn_inj.mp h) i)
    simpa [Nat.toUInt8, UInt8.toNat_ofNat'] using this
  have key : ∀ k ≤ 8, n % 256 ^ k = m % 256 ^ k := by
    intro k hk
    induction k with
    | zero => simp [Nat.mod_one]
    | succ k ih => rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (by omega), hd ⟨k, by omega⟩]
  have h8 := key 8 le_rfl
  rwa [Nat.mod_eq_of_lt (by norm_num at hn ⊢; omega), Nat.mod_eq_of_lt (by norm_num at hm ⊢; omega)]
    at h8

theorem ByteArray.eq_of_toList {q q' : ByteArray} (h : q.data.toList = q'.data.toList) :
    q = q' := by
  cases q; cases q'; simpa using h

/-- **The item codes are prefix-free**: two small items followed by anything give the same bytes
only if the items and the rests are equal. -/
theorem Item.enc_append_inj {x y : Item} (hx : x.small = true) (hy : y.small = true)
    {s t : List UInt8} (h : x.enc ++ s = y.enc ++ t) : x = y ∧ s = t := by
  cases x with
  | ans q a =>
    cases y with
    | ans q' a' =>
      simp only [Item.enc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨h1, h⟩ := List.append_inj h (by simp [enc64])
      have hq : q.size = q'.size :=
        enc64_inj (by simpa [Item.small] using hx) (by simpa [Item.small] using hy) h1
      obtain ⟨h2, h⟩ :=
        List.append_inj h (by rw [Array.length_toList, Array.length_toList]; exact hq)
      obtain ⟨h3, h4⟩ := List.append_inj h (by simp)
      exact ⟨by rw [ByteArray.eq_of_toList h2, Vector.toList_inj.mp h3], h4⟩
    | att _ => simp [Item.enc] at h
  | att g =>
    cases y with
    | ans _ _ => simp [Item.enc] at h
    | att g' =>
      simp only [Item.enc, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      exact ⟨by rw [Vector.toList_inj.mp h1], h2⟩

/-- **The list encoding is injective on bounded lists.** -/
theorem encList_inj : ∀ {xs ys : List Item}, Bounded xs → Bounded ys → encList xs = encList ys →
    xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by cases y <;> simp [Item.enc] at h
  | x :: _, [], _, _, h => by cases x <;> simp [Item.enc] at h
  | x :: xs, y :: ys, hx, hy, h => by
    obtain ⟨rfl, h'⟩ := Item.enc_append_inj (hx x (by simp)) (hy y (by simp)) (by simpa using h)
    rw [encList_inj hx.tail hy.tail h']

/-- **A `hashList` collision is a BLAKE2s collision**: two distinct bounded lists with one hash
give two distinct byte strings with one BLAKE2s-256 digest. -/
theorem hashList_coll {xs ys : List Item} (hx : Bounded xs) (hy : Bounded ys) (hne : xs ≠ ys)
    (h : hashList xs = hashList ys) :
    tagList :: encList xs ≠ tagList :: encList ys ∧
      blake2s256 (tagList :: encList xs) = blake2s256 (tagList :: encList ys) := by
  refine ⟨fun h' => hne (encList_inj hx hy (List.cons.inj h').2), ?_⟩
  have := congrArg (fun d : Digest => d.toArray.toList) h
  simpa [hashList, blake2sDigest] using this

/-! ## Reading a log -/

/-- The answer an event gives to `q`: `a` for `ans q a`, nothing otherwise. -/
def Ev.ansFor (q : ByteArray) : Ev → Option Digest
  | .ans q' a => if q' = q then some a else none
  | .cert _ => none

/-- The certified list an event records with hash `h`, if any. -/
def Ev.certFor (h : Digest) : Ev → Option (List Item)
  | .ans _ _ => none
  | .cert xs => if hashList xs = h then some xs else none

/-- The answer the log gives to `q`: its first `ans q _` event. -/
def firstAns (L : ALog) (q : ByteArray) : Option Digest := L.findSome? (Ev.ansFor q)

/-- The first certified list of the log whose hash is `h`. -/
def certOf (L : ALog) (h : Digest) : Option (List Item) := L.findSome? (Ev.certFor h)

/-- `h` is attested on `L`: some certified list of `L` has hash `h`. -/
def attested (L : ALog) (h : Digest) : Bool := (certOf L h).isSome

theorem certOf_spec {L : ALog} {h : Digest} {xs : List Item} (hc : certOf L h = some xs) :
    Ev.cert xs ∈ L ∧ hashList xs = h := by
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some hc
  cases e with
  | ans _ _ => simp [Ev.certFor] at hf
  | cert ys =>
    simp only [Ev.certFor, Option.ite_none_right_eq_some, Option.some.injEq] at hf
    obtain ⟨hh, rfl⟩ := hf
    exact ⟨he, hh⟩

theorem attested_iff {L : ALog} {h : Digest} :
    attested L h = true ↔ ∃ xs, Ev.cert xs ∈ L ∧ hashList xs = h := by
  constructor
  · intro ha
    obtain ⟨xs, hx⟩ := Option.isSome_iff_exists.mp ha
    exact ⟨xs, certOf_spec hx⟩
  · rintro ⟨xs, hx, rfl⟩
    cases hc : certOf L (hashList xs) with
    | some _ => simp [attested, hc]
    | none =>
      have := List.findSome?_eq_none_iff.mp hc (Ev.cert xs) hx
      simp [Ev.certFor] at this

theorem firstAns_append {P : ALog} (S : ALog) {q : ByteArray} {a : Digest}
    (h : firstAns P q = some a) : firstAns (P ++ S) q = some a := by
  simp [firstAns, List.findSome?_append, show P.findSome? (Ev.ansFor q) = some a from h]

theorem attested_append {P : ALog} (S : ALog) {h : Digest} (ha : attested P h = true) :
    attested (P ++ S) h = true := by
  obtain ⟨xs, hx, hh⟩ := attested_iff.mp ha
  exact attested_iff.mpr ⟨xs, List.mem_append_left _ hx, hh⟩

/-! ## Valid lists and well-formed logs -/

/-- An item is true of the log `L`: a small answer that is `L`'s first answer to its query, or a
hash attested on `L`. -/
def Item.OK (L : ALog) : Item → Prop
  | .ans q a => q.size < 2 ^ 64 ∧ firstAns L q = some a
  | .att h => attested L h = true

/-- **The service accepts `xs` on `L`**: every item is true of `L`. -/
def Valid (L : ALog) (xs : List Item) : Prop := ∀ x ∈ xs, x.OK L

/-- **A well-formed log**: every certification is valid on the log before it (the service checked
it). -/
def WF (L : ALog) : Prop := ∀ P xs S, L = P ++ Ev.cert xs :: S → Valid P xs

theorem Valid.bounded {L : ALog} {xs : List Item} (h : Valid L xs) : Bounded xs := fun x hx => by
  have := h x hx
  cases x with
  | ans q a => simpa [Item.small] using this.1
  | att _ => rfl

theorem Valid.append {P : ALog} (S : ALog) {xs : List Item} (h : Valid P xs) :
    Valid (P ++ S) xs := fun x hx => by
  have := h x hx
  cases x with
  | ans q a => exact ⟨this.1, firstAns_append S this.2⟩
  | att _ => exact attested_append S this

/-- In a well-formed log, every certified list is valid on the whole log. -/
theorem WF.valid_of_mem {L : ALog} (hW : WF L) {xs : List Item} (hx : Ev.cert xs ∈ L) :
    Valid L xs := by
  obtain ⟨P, S, rfl⟩ := List.append_of_mem hx
  simpa using (hW P xs S rfl).append (Ev.cert xs :: S)

theorem WF.nil : WF [] := fun P _ _ h => by cases P <;> simp at h

theorem WF.snoc {L : ALog} {e : Ev} (hW : WF L) (he : ∀ xs, e = .cert xs → Valid L xs) :
    WF (L ++ [e]) := by
  intro P xs S h
  rcases List.eq_nil_or_concat S with rfl | ⟨S', x, rfl⟩
  · obtain ⟨rfl, h'⟩ := List.append_inj' h rfl
    exact he xs (List.cons.inj h').1
  · have h' : L ++ [e] = (P ++ Ev.cert xs :: S') ++ [x] := by simpa using h
    obtain ⟨rfl, -⟩ := List.append_inj' h' rfl
    exact hW P xs S' rfl

/-- A fresh answer keeps a log well formed. -/
theorem WF.snoc_ans {L : ALog} (hW : WF L) (q : ByteArray) (a : Digest) :
    WF (L ++ [.ans q a]) := hW.snoc fun _ h => by cases h

/-- A valid certification keeps a log well formed. -/
theorem WF.snoc_cert {L : ALog} (hW : WF L) {xs : List Item} (hv : Valid L xs) :
    WF (L ++ [.cert xs]) := hW.snoc fun _ h => by cases h; exact hv

/-- A certified answer of a well-formed log is the log's answer. -/
theorem WF.ans_of_cert {L : ALog} (hW : WF L) {xs : List Item} (hx : Ev.cert xs ∈ L)
    {q : ByteArray} {a : Digest} (hq : Item.ans q a ∈ xs) : firstAns L q = some a :=
  (hW.valid_of_mem hx _ hq).2

/-! ## Query programs with attestation -/

/-- A computation that asks the oracle and the attestation service and returns an `α`. -/
inductive AProg (α : Type) where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Ask the oracle `q`, continue with its answer. -/
  | query (q : ByteArray) (k : Digest → AProg α)
  /-- Ask whether `h` is attested, continue with the bit. -/
  | attest (h : Digest) (k : Bool → AProg α)

/-- An oracle call of a run: a query, or an attestation request. -/
inductive Call where
  /-- The oracle query `q`. -/
  | query (q : ByteArray)
  /-- The attestation request for `h`. -/
  | attest (h : Digest)

/-- The answer a list of items gives to `q`: its first `ans q _` item. -/
def itemAns (xs : List Item) (q : ByteArray) : Option Digest :=
  xs.findSome? fun | .ans q' a => if q' = q then some a else none | .att _ => none

namespace AProg
variable {α : Type}

/-- **The verdict read from the log `L`**: `query q` is answered by `L`'s first answer to `q`
(`none` if there is none), `attest h` by whether `h` is attested on `L`. -/
def runLog (L : ALog) : AProg α → Option α
  | ret a => some a
  | query q k => (firstAns L q).bind fun a => (k a).runLog L
  | attest h k => (k (attested L h)).runLog L

/-- **The verdict read from a list of items** (a child's run inside a node's circuit): `query q`
is answered by the first `ans q _` item, `attest h` succeeds only if `att h` is an item. -/
def runItems (xs : List Item) : AProg α → Option α
  | ret a => some a
  | query q k => (itemAns xs q).bind fun a => (k a).runItems xs
  | attest h k => if Item.att h ∈ xs then (k true).runItems xs else none

/-- The oracle calls of a run against the oracle function `H` and the attest predicate `A`. -/
def calls (H : ByteArray → Digest) (A : Digest → Bool) : AProg α → List Call
  | ret _ => []
  | query q k => .query q :: (k (H q)).calls H A
  | attest h k => .attest h :: (k (A h)).calls H A

end AProg

theorem itemAns_mem {xs : List Item} {q : ByteArray} {a : Digest} (h : itemAns xs q = some a) :
    Item.ans q a ∈ xs := by
  obtain ⟨x, hx, hf⟩ := List.exists_of_findSome?_eq_some h
  cases x with
  | ans q' a' =>
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact hx
  | att _ => simp at hf

/-- **Lifting**: a verdict read from a list that is valid on `L` is the verdict read from `L`. -/
theorem runItems_valid {α : Type} {L : ALog} {xs : List Item} (hv : Valid L xs) :
    ∀ {p : AProg α} {b : α}, p.runItems xs = some b → p.runLog L = some b
  | .ret _, _, h => h
  | .query q k, b, h => by
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [AProg.runLog, (hv _ (itemAns_mem ha)).2, Option.bind_some]
    exact runItems_valid hv h
  | .attest g k, b, h => by
    simp only [AProg.runItems] at h
    split_ifs at h with hg
    simp only [AProg.runLog, show attested L g = true from hv _ hg]
    exact runItems_valid hv h

/-! ## The embedding of the contract's model -/

/-- A contract query program as an attested one (it never attests). -/
def _root_.RecursionFast.OProg.toA {α : Type} : OProg α → AProg α
  | .ret a => .ret a
  | .query q k => .query q fun a => (k a).toA

/-- The contract log of a log's answers: its `ans` events, in order. -/
def ansLog (L : ALog) : Log := L.filterMap fun | .ans q a => some (q, a) | .cert _ => none

@[simp] theorem ansLog_append (L S : ALog) : ansLog (L ++ S) = ansLog L ++ ansLog S :=
  List.filterMap_append

@[simp] theorem ansLog_ans (q : ByteArray) (a : Digest) : ansLog [.ans q a] = [(q, a)] := rfl

@[simp] theorem ansLog_cert (xs : List Item) : ansLog [.cert xs] = [] := rfl

theorem ansLog_length (L : ALog) : (ansLog L).length ≤ L.length := List.length_filterMap_le _ _

/-- The first answer of a log is the first answer of its contract log. -/
theorem firstAns_eq (L : ALog) (q : ByteArray) :
    firstAns L q = Relativized.firstAns (ansLog L) q := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    cases e with
    | ans q' a =>
      change List.findSome? (Ev.ansFor q) (Ev.ans q' a :: L) =
        Option.map Prod.snd (List.find? (fun e => decide (e.1 = q)) ((q', a) :: ansLog L))
      rw [List.findSome?_cons, List.find?_cons]
      by_cases hq : q' = q
      · simp [Ev.ansFor, hq]
      · simp only [Ev.ansFor, hq, ite_false, decide_false]; exact ih
    | cert xs => exact ih

/-- **A lifted program reads from a log what the original reads from its answers.** -/
theorem toA_runLog {α : Type} (L : ALog) (p : OProg α) : p.toA.runLog L = p.runLog (ansLog L) := by
  induction p with
  | ret a => rfl
  | query q k ih =>
    simp only [OProg.toA, AProg.runLog, OProg.runLog, firstAns_eq, Relativized.firstAns,
      Option.bind_map]
    congr 1; funext e; exact ih e.2

/-- A lifted program makes the original's queries and no attestation request. -/
theorem toA_calls {α : Type} (H : ByteArray → Digest) (A : Digest → Bool) (p : OProg α) :
    p.toA.calls H A = (p.queries H).map Call.query := by
  induction p with
  | ret a => rfl
  | query q k ih => simp [OProg.toA, AProg.calls, OProg.queries, ih]

end RecursionFast.Explore.Attested
