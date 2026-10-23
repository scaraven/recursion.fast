/-
  RecursionFast.Library.Fast  (UNTRUSTED, kernel-checked)

  **The badge path at word level** (C9, C10, C-m3, V4-A7 (d)). The harness runs the compiled
  `Submission.acc` on every proof under a CPU-time cap (V4-12); the contract's BLAKE2s is a
  readable reference (about 5 µs per compression compiled, `logs/A-speed-*.log`). This file gives
  twins of every hash on that path, each proved equal to the contract's function, built on the
  word-level compression and the byte-array message path of `Library/Blake2sFast.lean` (about
  0.4 µs per compression):

  * `traceDigestF` (the trace's bytes built in a byte array) = `traceDigest`;
  * `wotsStepF`, `wotsChainF`, `wotsEndsF`, `wotsLeafF`, `sigNodeF`, `sigRootF`, `SigOkF` =
    their contract counterparts;
  * `chainStepF`, `chainEndF`, `leafStmtF`, `nodeStmtF` = the relation's hashes (a verifier that
    recomputes chains, such as the witness-sending one, runs these);
  * **`Submission.accF`** = `Submission.acc` (`accF_eq`): the harness may run `accF` and the
    record is about `acc`.
  Measured numbers are in `docs/v4/stages/A-contract-RESULT.md`.
-/
import RecursionFast.Contract.Certificate
import RecursionFast.Library.Blake2sFast

namespace RecursionFast
open Blake2s

/-! ## Building byte arrays -/

/-- Push the bytes of a list onto a byte array. -/
def pushAll (b : ByteArray) (l : List UInt8) : ByteArray := l.foldl ByteArray.push b

theorem pushAll_data (b : ByteArray) (l : List UInt8) :
    (pushAll b l).data.toList = b.data.toList ++ l := by
  induction l generalizing b with
  | nil => simp [pushAll]
  | cons x l ih =>
    simp only [pushAll, List.foldl_cons] at ih ⊢
    rw [ih, ByteArray.data_push]
    simp

@[simp] theorem emptyWithCapacity_data (n : ℕ) : (ByteArray.emptyWithCapacity n).data = #[] := rfl

/-- Push the 8 bytes of `enc64 n` (no intermediate list). -/
def pushU64 (b : ByteArray) (n : ℕ) : ByteArray :=
  (((((((b.push n.toUInt8).push (n / 256).toUInt8).push (n / 256 ^ 2).toUInt8).push
    (n / 256 ^ 3).toUInt8).push (n / 256 ^ 4).toUInt8).push (n / 256 ^ 5).toUInt8).push
    (n / 256 ^ 6).toUInt8).push (n / 256 ^ 7).toUInt8

theorem pushU64_data (b : ByteArray) (n : ℕ) :
    (pushU64 b n).data.toList = b.data.toList ++ enc64 n := by
  simp [pushU64, ByteArray.data_push, enc64, List.ofFn_succ]

/-- Append the 32 bytes of a digest. -/
def pushDigest (b : ByteArray) (d : Digest) : ByteArray := b ++ ⟨d.toArray⟩

theorem pushDigest_data (b : ByteArray) (d : Digest) :
    (pushDigest b d).data.toList = b.data.toList ++ d.toList := by
  rw [pushDigest, ByteArray.data_append, Array.toList_append]; rfl

/-! ## The trace digest -/

/-- The bytes `traceDigest` hashes (`tagTrace ‖ traceBytes tr`), built in a byte array. -/
def traceBytesB (tr : Trace) : ByteArray :=
  tr.foldl (fun b e => pushDigest (pushU64 b e.1.size ++ e.1) e.2)
    ((ByteArray.emptyWithCapacity (1 + 140 * tr.length)).push tagTrace)

theorem traceBytesB_data (tr : Trace) :
    (traceBytesB tr).data.toList = tagTrace :: traceBytes tr := by
  suffices h : ∀ (b : ByteArray) (tr : Trace), (tr.foldl (fun b e =>
      pushDigest (pushU64 b e.1.size ++ e.1) e.2) b).data.toList =
      b.data.toList ++ traceBytes tr by
    rw [traceBytesB, h]; simp [ByteArray.data_push]
  intro b tr
  induction tr generalizing b with
  | nil => simp [traceBytes]
  | cons e tr ih =>
    rw [List.foldl_cons, ih, pushDigest_data, ByteArray.data_append, Array.toList_append,
      pushU64_data]
    simp [traceBytes, List.append_assoc]

/-- `traceDigest` through the byte-array path. -/
def traceDigestF (tr : Trace) : Digest := digestB (traceBytesB tr)

theorem traceDigestF_eq (tr : Trace) : traceDigestF tr = traceDigest tr := by
  rw [traceDigestF, digestB_eq, traceBytesB_data, traceDigest]

/-! ## The signature check -/

/-- `wotsStep` through the byte-array path. -/
def wotsStepF (j i s : ℕ) (x : Digest) : Digest :=
  digestB (pushDigest (((pushU64 ((ByteArray.emptyWithCapacity 43).push tagWots) j).push
    i.toUInt8).push s.toUInt8) x)

theorem wotsStepF_eq : wotsStepF = wotsStep := by
  funext j i s x
  simp [wotsStepF, wotsStep, digestB_eq, pushDigest_data, pushU64_data, ByteArray.data_push]

/-- `wotsChain` with `wotsStepF`. -/
def wotsChainF (j i s : ℕ) : ℕ → Digest → Digest
  | 0, x => x
  | n + 1, x => wotsChainF j i (s + 1) n (wotsStepF j i s x)

theorem wotsChainF_eq : wotsChainF = wotsChain := by
  funext j i s n x
  induction n generalizing s x with
  | zero => rfl
  | succ n ih => rw [wotsChainF, wotsChain, ih, wotsStepF_eq]

/-- `wotsLeaf` through the byte-array path. -/
def wotsLeafF (j : ℕ) (ends : List Digest) : Digest :=
  digestB (ends.foldl pushDigest (pushU64 ((ByteArray.emptyWithCapacity 4265).push tagWotsLeaf) j))

theorem foldl_pushDigest_data (b : ByteArray) (ds : List Digest) :
    (ds.foldl pushDigest b).data.toList = b.data.toList ++ ds.flatMap Vector.toList := by
  induction ds generalizing b with
  | nil => simp
  | cons d ds ih => simp [ih, pushDigest_data]

theorem wotsLeafF_eq : wotsLeafF = wotsLeaf := by
  funext j ends
  simp [wotsLeafF, wotsLeaf, digestB_eq, foldl_pushDigest_data, pushU64_data, ByteArray.data_push]

/-- `sigNode` through the byte-array path. -/
def sigNodeF (l r : Digest) : Digest :=
  digestB (pushDigest (pushDigest ((ByteArray.emptyWithCapacity 65).push tagSigNode) l) r)

/-- `sigRoot` with `sigNodeF`. -/
def sigRootF : ℕ → Digest → List Digest → Digest
  | _, x, [] => x
  | j, x, s :: p => sigRootF (j / 2) (if j % 2 = 0 then sigNodeF x s else sigNodeF s x) p

theorem sigNodeF_eq : sigNodeF = sigNode := by
  funext l r
  simp [sigNodeF, sigNode, digestB_eq, pushDigest_data, ByteArray.data_push]

theorem sigRootF_eq : sigRootF = sigRoot := by
  funext j x p
  induction p generalizing j x with
  | nil => rfl
  | cons s p ih => rw [sigRootF, sigRoot, ih, sigNodeF_eq]

/-- `SigOk` with the fast hashes. -/
def SigOkF (vk m : Digest) (σ : Sig) : Bool :=
  decide (σ.idx < 2 ^ sigHeight) && decide (σ.ots.length = wotsLen) &&
    decide (σ.path.length = sigHeight) &&
    decide (sigRootF σ.idx (wotsLeafF σ.idx (((wotsDigits m).zip σ.ots).mapIdx fun i e =>
      wotsChainF σ.idx i e.1 (3 - e.1) e.2)) σ.path = vk)

theorem SigOkF_eq : SigOkF = SigOk := by
  funext vk m σ
  simp only [SigOkF, SigOk, sigRootF_eq, wotsChainF_eq, wotsLeafF_eq, wotsEnds]
  rfl

/-! ## The relation's hashes -/

/-- `chainStep` through the byte-array path. -/
def chainStepF (d : Digest) : Digest :=
  digestB (pushDigest ((ByteArray.emptyWithCapacity 33).push tagChain) d)

/-- `chainEnd`, `n` steps of `chainStepF`. -/
def chainEndF (s : Digest) : ℕ → Digest
  | 0 => s
  | n + 1 => chainEndF (chainStepF s) n

/-- `leafStmt` through the byte-array path. -/
def leafStmtF (h : Digest) (n : ℕ) : Digest :=
  digestB (pushU64 (pushDigest ((ByteArray.emptyWithCapacity 41).push tagLeaf) h) n)

/-- `nodeStmt` through the byte-array path. -/
def nodeStmtF (c₁ c₂ : Digest) : Digest :=
  digestB (pushDigest (pushDigest ((ByteArray.emptyWithCapacity 65).push tagNode) c₁) c₂)

theorem chainStepF_eq : chainStepF = chainStep := by
  funext d
  simp [chainStepF, chainStep, digestB_eq, pushDigest_data, ByteArray.data_push]

theorem chainEndF_eq : chainEndF = chainEnd := by
  funext s n
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [chainEndF, ih, chainStepF_eq, chainEnd, chainEnd,
      Function.iterate_succ_apply]

theorem leafStmtF_eq : leafStmtF = leafStmt := by
  funext h n
  simp [leafStmtF, leafStmt, digestB_eq, pushU64_data, pushDigest_data, ByteArray.data_push]

theorem nodeStmtF_eq : nodeStmtF = nodeStmt := by
  funext a b
  simp [nodeStmtF, nodeStmt, digestB_eq, pushDigest_data, ByteArray.data_push]

/-! ## Acceptance -/

/-- **`acc` with the fast hashes**: what the harness runs. -/
def Submission.accF (S : Submission) (vk c : Digest) (p : Signed) : Bool :=
  decide (p.π.size ≤ proofCap) && decide (p.tr.length ≤ S.qV) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOkF vk (traceDigestF p.tr) p.σ &&
    decide ((S.V vk c p.π).runSeq p.tr = some true)

/-- **The harness's `accF` is the contract's `acc`.** -/
theorem accF_eq (S : Submission) : S.accF = S.acc := by
  funext vk c p
  simp only [Submission.accF, Submission.acc, SigOkF_eq, traceDigestF_eq]

end RecursionFast
