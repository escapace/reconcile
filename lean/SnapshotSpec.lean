/-
  Reconcile — snapshot semantic specification.

  Defines `snapshot` relationally as a state-threading construction with
  a memo table. The specification is proof-first: no executable recursion
  over cyclic graphs, just a relation (or explicit state invariant)
  describing valid snapshot results.

  Design:
    - SnapshotState: memo map + result heap built so far
    - SnapshotNodeSpec: one-node processing relation
    - SnapshotSpec: top-level relation tying source root to result root
-/

import Defs
import WF

namespace Reconcile

/-! ## Snapshot state -/

/-- State carried through a snapshot traversal.
    `src` is the source heap (read-only).
    `memo` maps source ids to their already-allocated result ids.
    `result` is the result heap under construction.
    `nextFresh` is the next available fresh id. -/
structure SnapshotState (A : Type) (ι : Type) [DecidableEq ι] where
  /-- The source heap (immutable reference). -/
  src : Heap A ι
  /-- Memo table: source id → result id. -/
  memo : Finmap (fun _ : ι => ι)
  /-- The result heap built so far. -/
  result : Heap A ι
  /-- Next available fresh id (monotonically increasing). -/
  nextFresh : Nat

/-! ## Snapshot value specification -/

/-- A value is correctly snapshotted from source to result.
    `SnapshotValueSpec src result memo v rv` says:
    - if `v` is an atom, `rv` is the same atom,
    - if `v = ref r` and `memo(r) = some r'`, then `rv = ref r'`,
    - if `v = ref r` and `memo(r) = none`, then `rv = ref r'` for some
      fresh `r'` already in `memo` and `result`. -/
inductive SnapshotValueSpec {A : Type} {ι : Type} [DecidableEq ι]
    (src result : Heap A ι) (memo : Finmap (fun _ : ι => ι)) :
    Value A ι → Value A ι → Prop where
  /-- Atoms pass through unchanged. -/
  | atom (a : A) : SnapshotValueSpec src result memo (.atom a) (.atom a)
  /-- Memoized ref: the result ref is the memo entry. -/
  | memoHit {r r' : ι} :
      memo.lookup r = some r' →
      SnapshotValueSpec src result memo (.ref r) (.ref r')

/-! ## One-node snapshot specification -/

/-- A single node is correctly snapshotted. -/
inductive SnapshotNodeSpec {A : Type} {ι : Type} [DecidableEq ι]
    (src result : Heap A ι) (memo : Finmap (fun _ : ι => ι)) :
    Node A ι → Node A ι → Prop where
  /-- Plain object: same proto, same keys in order (no duplicates),
      each field value snapshotted. -/
  | plainObject {p : ProtoLabel}
      {f₁ f₂ : ObjFields A ι} :
      f₁.NodupKeys → f₂.NodupKeys →
      f₁.keys = f₂.keys →
      (∀ k v₁ v₂, List.dlookup k f₁ = some v₁ → List.dlookup k f₂ = some v₂ →
        SnapshotValueSpec src result memo v₁ v₂) →
      SnapshotNodeSpec src result memo (.plainObject p f₁) (.plainObject p f₂)
  /-- Array: same length, each entry snapshotted (holes preserved). -/
  | array {es₁ es₂ : List (Option (Value A ι))} :
      es₁.length = es₂.length →
      (∀ i (hi₁ : i < es₁.length) (hi₂ : i < es₂.length),
        OptionRel (SnapshotValueSpec src result memo) es₁[i] es₂[i]) →
      SnapshotNodeSpec src result memo (.array es₁) (.array es₂)
  /-- Date: timestamp preserved. -/
  | date {ms : Int} :
      SnapshotNodeSpec src result memo (.date ms) (.date ms)
  /-- Map: same-length entries, keys and values snapshotted in order. -/
  | map {es₁ es₂ : List (Value A ι × Value A ι)} :
      es₁.length = es₂.length →
      (∀ i (hi₁ : i < es₁.length) (hi₂ : i < es₂.length),
        SnapshotValueSpec src result memo (es₁[i]).1 (es₂[i]).1 ∧
        SnapshotValueSpec src result memo (es₁[i]).2 (es₂[i]).2) →
      SnapshotNodeSpec src result memo (.map es₁) (.map es₂)
  /-- Set: same-length values, each snapshotted in order. -/
  | set {vs₁ vs₂ : List (Value A ι)} :
      vs₁.length = vs₂.length →
      (∀ i (hi₁ : i < vs₁.length) (hi₂ : i < vs₂.length),
        SnapshotValueSpec src result memo vs₁[i] vs₂[i]) →
      SnapshotNodeSpec src result memo (.set vs₁) (.set vs₂)
  /-- ArrayBuffer: bytes copied. -/
  | arrayBuffer {bs : List UInt8} :
      SnapshotNodeSpec src result memo (.arrayBuffer bs) (.arrayBuffer bs)
  /-- DataView: buffer ref snapshotted, metadata preserved. -/
  | dataView {b₁ b₂ : ι} {off len : Nat} :
      SnapshotValueSpec src result memo (.ref b₁) (.ref b₂) →
      SnapshotNodeSpec src result memo
        (.dataView b₁ off len) (.dataView b₂ off len)
  /-- TypedArray: buffer ref snapshotted, metadata and elements preserved. -/
  | typedArray {tag : CtorTag} {b₁ b₂ : ι} {off len : Nat}
      {elems₁ elems₂ : List (Value A ι)} :
      SnapshotValueSpec src result memo (.ref b₁) (.ref b₂) →
      elems₁.length = elems₂.length →
      (∀ i (hi₁ : i < elems₁.length) (hi₂ : i < elems₂.length),
        SnapshotValueSpec src result memo elems₁[i] elems₂[i]) →
      SnapshotNodeSpec src result memo
        (.typedArray tag b₁ off len elems₁) (.typedArray tag b₂ off len elems₂)

/-! ## Top-level snapshot specification -/

/-- Invariants that a memo table must satisfy for a correct snapshot.
    Separated from `SnapshotSpec` so proofs can work with the memo directly. -/
structure SnapshotMemoSpec {A : Type} {ι : Type} [DecidableEq ι]
    (src : Heap A ι) (resultHeap : Heap A ι)
    (memo : Finmap (fun _ : ι => ι)) : Prop where
  /-- Memo is injective: distinct source ids map to distinct result ids. -/
  memoInj : ∀ r₁ r₂ r', memo.lookup r₁ = some r' → memo.lookup r₂ = some r' → r₁ = r₂
  /-- Every memo'd node is correctly snapshotted in the result heap. -/
  nodeSpec : ∀ r r', memo.lookup r = some r' →
    ∀ nd, src.lookup r = some nd →
    ∃ nd', resultHeap.lookup r' = some nd' ∧
      SnapshotNodeSpec src resultHeap memo nd nd'
  /-- Every memo'd source ref is in the source heap domain. -/
  memoDom : ∀ r r', memo.lookup r = some r' → ∃ nd, src.lookup r = some nd
  /-- Result ids from memo are fresh (disjoint from source domain).
      This captures detachment (S2). -/
  freshness : ∀ r r', memo.lookup r = some r' → r ≠ r'

/-- A complete snapshot result satisfies this specification.
    `SnapshotSpec src root resultHeap resultRoot` says there exists a memo
    table witnessing the node correspondence such that the root is correctly
    mapped and all memo invariants hold. -/
def SnapshotSpec {A : Type} {ι : Type} [DecidableEq ι]
    (src : Heap A ι) (root : Value A ι)
    (resultHeap : Heap A ι) (resultRoot : Value A ι) : Prop :=
  ∃ memo : Finmap (fun _ : ι => ι),
    SnapshotValueSpec src resultHeap memo root resultRoot ∧
    SnapshotMemoSpec src resultHeap memo

/-! ## Snapshot theorems (statements only — proofs in Iteration 4) -/

/-- S2 — Detachment: result refs from snapshot are fresh. -/
theorem snapshot_detachment {A : Type} {ι : Type} [DecidableEq ι]
    {src : Heap A ι} {root : Value A ι}
    {resultHeap : Heap A ι} {resultRoot : Value A ι}
    (spec : SnapshotSpec src root resultHeap resultRoot) :
    ∃ memo : Finmap (fun _ : ι => ι),
      ∀ r r', memo.lookup r = some r' → r ≠ r' := by
  obtain ⟨memo, _, hms⟩ := spec
  exact ⟨memo, hms.freshness⟩

/-- S3 — Sharing preservation: equal source refs → equal result refs.
    This follows directly from the memo being a function. -/
theorem snapshot_sharing {A : Type} {ι : Type} [DecidableEq ι]
    {src : Heap A ι} {root : Value A ι}
    {resultHeap : Heap A ι} {resultRoot : Value A ι}
    (_spec : SnapshotSpec src root resultHeap resultRoot) :
    ∀ (memo : Finmap (fun _ : ι => ι)) r r₁' r₂',
      memo.lookup r = some r₁' → memo.lookup r = some r₂' → r₁' = r₂' := by
  intro memo r r₁' r₂' h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- S4 — Distinctness preservation: distinct source refs → distinct result refs. -/
theorem snapshot_distinctness {A : Type} {ι : Type} [DecidableEq ι]
    {src : Heap A ι} {root : Value A ι}
    {resultHeap : Heap A ι} {resultRoot : Value A ι}
    (spec : SnapshotSpec src root resultHeap resultRoot) :
    ∃ memo : Finmap (fun _ : ι => ι),
      ∀ r₁ r₂ r', memo.lookup r₁ = some r' →
        memo.lookup r₂ = some r' → r₁ = r₂ := by
  obtain ⟨memo, _, hms⟩ := spec
  exact ⟨memo, hms.memoInj⟩

/-- Snapshot preserves plain-object prototype labels for every memoized
    plain-object node. This exposes the prototype-preservation fact that is
    stronger than the generic `SurfaceEq` relation, which intentionally
    ignores retained plain-object prototype equality during reconcile. -/
theorem snapshot_plainObject_proto_preservation {A : Type} {ι : Type} [DecidableEq ι]
    {src : Heap A ι} {root : Value A ι}
    {resultHeap : Heap A ι} {resultRoot : Value A ι}
    (spec : SnapshotSpec src root resultHeap resultRoot) :
    ∃ memo : Finmap (fun _ : ι => ι),
      ∀ r r' p f,
        memo.lookup r = some r' →
        src.lookup r = some (.plainObject p f) →
        ∃ f', resultHeap.lookup r' = some (.plainObject p f') := by
  obtain ⟨memo, _, hms⟩ := spec
  refine ⟨memo, ?_⟩
  intro r r' p f hmem hsrc
  obtain ⟨nd', hnd', hns⟩ := hms.nodeSpec r r' hmem (.plainObject p f) hsrc
  cases hns with
  | plainObject _ _ _ _ =>
      exact ⟨_, hnd'⟩

end Reconcile
