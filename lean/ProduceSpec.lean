/-
  Produce draft layer — relational specification.

  This file gives a proof-first specification of draft execution and
  finalization. It stays intentionally abstract: the goal is to define the
  semantic contract that the runtime must satisfy, not to formalize JavaScript
  proxy traps or engine internals.
-/

import ProduceDefs

namespace Reconcile

/-- Proof-facing semantic contract for a finalized plain-object node produced by
    draft execution. This captures the semantic facts the produce theorem surface
    needs for delete and untouched-key reasoning. -/
structure ObjectDraftNodeSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (touches : DraftTouchWitness A) (basePath : DraftPath)
    (curFields : ObjFields A CurId)
    (nextFields : ObjFields A NextId) where
  deletedKeyAbsent : ∀ k,
    touches.deletedPathAt (basePath ++ [DraftPathElem.objectKey k]) →
    List.dlookup k nextFields = none
  untouchedKeyPreserved : ∀ k cv,
    List.dlookup k curFields = some cv →
    touches.unchangedPath (basePath ++ [DraftPathElem.objectKey k]) →
    ∃ nv, List.dlookup k nextFields = some nv ∧ SurfaceEq curHeap nextHeap cv nv

/-- Proof-facing semantic contract for a finalized array node produced by draft
    execution. The content is intentionally abstract but records the facts later
    produce proofs need: tracked writes, holes, truncation, and untouched-slot
    preservation. -/
structure ArrayDraftNodeSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (touches : DraftTouchWitness A) (basePath : DraftPath)
    (curEntries : List (Option (Value A CurId)))
    (nextEntries : List (Option (Value A NextId))) where
  /-- Includes indirect descendant/alias effects on this slot. -/
  touchedIndex : Nat → Prop
  writeTracked : ∀ i v,
    ArrayDraftOp.write i v ∈ touches.arrayOpsAt basePath → touchedIndex i
  holeTracked : ∀ i,
    ArrayDraftOp.hole i ∈ touches.arrayOpsAt basePath → touchedIndex i
  truncateTracked : ∀ len,
    touches.arrayLengthAt basePath = some len →
      nextEntries.length = len
  untouchedIndexPreserved : ∀ i (hiCur : i < curEntries.length)
      (hiNext : i < nextEntries.length),
      ¬ touchedIndex i →
      OptionRel (SurfaceEq curHeap nextHeap) curEntries[i] nextEntries[i]

/-- Captured map order is authoritative. Normalized keys are unique; execution
    of individual collection operations is outside this adapter boundary. -/
structure MapDraftNodeSpec {A : Type}
    (nextEntries : List (Value A NextId × Value A NextId)) where
  keysUnique : nextEntries.Pairwise (fun a b => a.1 ≠ b.1)

/-- Captured set order is authoritative, with normalized unique members. -/
structure SetDraftNodeSpec {A : Type}
    (nextValues : List (Value A NextId)) where
  valuesUnique : nextValues.Pairwise (fun a b => a ≠ b)

/-- Draft execution specification.

    This is the conditional proof-facing contract for standalone `produce`.
    It does not certify proxy traps, external recipe writes or capture observations.
    It packages:

    - one finalized next graph,
    - the root return mode,
    - access/touch/copy bookkeeping,
    - a current→next preservation witness,
    - abstract container-effect contracts.
-/
structure DraftExecSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (curRoot : Value A CurId)
    (nextHeap : Heap A NextId) (nextRoot : Value A NextId) where
  returnMode : DraftReturnMode A NextId
  touches : DraftTouchWitness A
  finalizeWitness : FinalizeWitness
  nextHeapWF : HeapWF nextHeap
  nextRootWF : RootWF nextHeap nextRoot
  /-- If the recipe returned an explicit replacement value, that value is the
      returned next root. -/
  returnModeSpec : match returnMode with
    | .finalized => True
    | .replaced v => nextRoot = v
  /-- Lazy child-draft creation: child drafts only exist at accessed paths. -/
  lazyChildDrafts : ∀ p, touches.childDraftAt p → touches.accessed p
  /-- This entire abstract execution contains no writes through any alias. -/
  readOnly : Prop
  /-- Read non-interference: a wholly read-only structural execution does not
      witness a modification or copy allocation at the denoted node. -/
  readNonInterference : ∀ p c,
      readOnly → touches.pureReadAt p →
      touches.pathNode p c →
      ¬ touches.modifiedNode c ∧ ¬ touches.copiedNode c
  /-- Copy-on-write requirement: the abstract copy predicate and the
      abstract modified predicate coincide at the node level. -/
  copyOnWrite : ∀ c, touches.copiedNode c ↔ touches.modifiedNode c
  /-- Modification propagates to ancestors in the current graph parent chain. -/
  parentPropagation : ∀ c p,
      touches.parentOf c p →
      touches.modifiedNode c →
      touches.modifiedNode p
  /-- Explicit delete and assignment-of-undefined are distinct semantic cases. -/
  deleteNotUndefinedAssign : ∀ p,
      touches.deletedPathAt p →
      ¬ touches.assignedUndefinedAt p
  undefinedAssignNotDelete : ∀ p,
      touches.assignedUndefinedAt p →
      ¬ touches.deletedPathAt p
  /-- Untouched preserved regions are related across current and next via the
      finalization witness. -/
  untouchedPreserved : ∀ c n,
      finalizeWitness.preserve.lookup c = some n →
      touches.unchangedRegion c →
      SurfaceEq curHeap nextHeap (.ref c) (.ref n)
  /-- Plain-object effects are captured by an abstract finalized-object
      contract. -/
  objectEffects : ∀ p c n pCur pNext curFields nextFields,
      touches.pathNode p c →
      finalizeWitness.preserve.lookup c = some n →
      curHeap.lookup c = some (.plainObject pCur curFields) →
      nextHeap.lookup n = some (.plainObject pNext nextFields) →
      ObjectDraftNodeSpec curHeap nextHeap touches p curFields nextFields
  /-- Array effects are captured by an abstract finalized-array contract. -/
  arrayEffects : ∀ p c n curEntries nextEntries,
      touches.pathNode p c →
      finalizeWitness.preserve.lookup c = some n →
      curHeap.lookup c = some (.array curEntries) →
      nextHeap.lookup n = some (.array nextEntries) →
      ArrayDraftNodeSpec curHeap nextHeap touches p curEntries nextEntries
  /-- Map effects are captured by an abstract finalized-map contract. -/
  mapEffects : ∀ p c n curEntries nextEntries,
      touches.pathNode p c →
      finalizeWitness.preserve.lookup c = some n →
      curHeap.lookup c = some (.map curEntries) →
      nextHeap.lookup n = some (.map nextEntries) →
      MapDraftNodeSpec nextEntries
  /-- Set effects are captured by an abstract finalized-set contract. -/
  setEffects : ∀ p c n curValues nextValues,
      touches.pathNode p c →
      finalizeWitness.preserve.lookup c = some n →
      curHeap.lookup c = some (.set curValues) →
      nextHeap.lookup n = some (.set nextValues) →
      SetDraftNodeSpec nextValues

end Reconcile
