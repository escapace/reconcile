/-
  Patch draft layer — relational specification.

  This file gives a proof-first specification of draft execution and
  finalization. It stays intentionally abstract: the goal is to define the
  semantic contract that the runtime must satisfy, not to formalize JavaScript
  proxy traps or engine internals.
-/

import PatchDraftDefs

namespace Reconcile

/-- Proof-facing semantic contract for a finalized plain-object node produced by
    draft execution. This captures the semantic facts the patch theorem surface
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
    ¬ touches.touchedPath (basePath ++ [DraftPathElem.objectKey k]) →
    ∃ nv, List.dlookup k nextFields = some nv ∧ SurfaceEq curHeap nextHeap cv nv

/-- Proof-facing semantic contract for a finalized array node produced by draft
    execution. The content is intentionally abstract but records the facts later
    patch proofs need: tracked writes, holes, truncation, and untouched-slot
    preservation. -/
structure ArrayDraftNodeSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (touches : DraftTouchWitness A) (basePath : DraftPath)
    (curEntries : List (Option (Value A CurId)))
    (nextEntries : List (Option (Value A NextId))) where
  touchedIndex : Nat → Prop
  writeTracked : ∀ i v,
    ArrayDraftOp.write i v ∈ touches.arrayOpsAt basePath → touchedIndex i
  holeTracked : ∀ i,
    ArrayDraftOp.hole i ∈ touches.arrayOpsAt basePath → touchedIndex i
  truncateTracked : ∀ len,
    ArrayDraftOp.truncate len ∈ touches.arrayOpsAt basePath →
      nextEntries.length = len
  untouchedIndexPreserved : ∀ i (hiCur : i < curEntries.length)
      (hiNext : i < nextEntries.length),
      ¬ touchedIndex i →
      OptionRel (SurfaceEq curHeap nextHeap) curEntries[i] nextEntries[i]

/-- Proof-facing semantic contract for a finalized map node produced by draft
    execution. This records the tracked keyed mutations and leaves the exact
    final keyed sequence as the semantic result of those mutations. -/
structure MapDraftNodeSpec {A : Type}
    (touches : DraftTouchWitness A) (basePath : DraftPath)
    (nextEntries : List (Value A NextId × Value A NextId)) where
  setTracked : ∀ k v,
    MapDraftOp.set k v ∈ touches.mapOpsAt basePath → True
  deleteTracked : ∀ k,
    MapDraftOp.delete k ∈ touches.mapOpsAt basePath → True
  clearTracked : MapDraftOp.clear ∈ touches.mapOpsAt basePath → True
  finalizedSequence : True

/-- Proof-facing semantic contract for a finalized set node produced by draft
    execution. This records the tracked membership mutations and leaves the
    exact final value sequence as the semantic result of those mutations. -/
structure SetDraftNodeSpec {A : Type}
    (touches : DraftTouchWitness A) (basePath : DraftPath)
    (nextValues : List (Value A NextId)) where
  addTracked : ∀ v,
    SetDraftOp.add v ∈ touches.setOpsAt basePath → True
  deleteTracked : ∀ v,
    SetDraftOp.delete v ∈ touches.setOpsAt basePath → True
  clearTracked : SetDraftOp.clear ∈ touches.setOpsAt basePath → True
  finalizedSequence : True

/-- Draft execution specification.

    This is the central proof-facing contract for the replacement patch model.
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
      published next root. -/
  returnModeSpec : match returnMode with
    | .finalized => True
    | .replaced v => nextRoot = v
  /-- Lazy child-draft creation: child drafts only exist at accessed paths. -/
  lazyChildDrafts : ∀ p, touches.childDraftAt p → touches.accessed p
  /-- Read non-interference: a pure read path does not itself witness a direct
      modification or copy allocation of the node denoted by that path. -/
  readNonInterference : ∀ p c,
      touches.pureReadAt p →
      touches.pathNode p c →
      ¬ touches.modifiedNode c ∧ ¬ touches.copiedNode c
  /-- Copy-on-write allocation: the abstract copy-allocation predicate and the
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
      ¬ touches.touchedNode c →
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
      MapDraftNodeSpec touches p nextEntries
  /-- Set effects are captured by an abstract finalized-set contract. -/
  setEffects : ∀ p c n curValues nextValues,
      touches.pathNode p c →
      finalizeWitness.preserve.lookup c = some n →
      curHeap.lookup c = some (.set curValues) →
      nextHeap.lookup n = some (.set nextValues) →
      SetDraftNodeSpec touches p nextValues

end Reconcile
