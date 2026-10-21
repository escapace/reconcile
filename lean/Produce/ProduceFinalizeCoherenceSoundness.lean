import Produce.ProduceFinalizeCoherence

/-!
# Produce draft layer: finalization coherence theorems

The draft-level theorems the implementation is read against. They project the
finalization-coherence boundary carried by `FinalizeCoherenceSpec` without introducing any
runtime-mechanism semantics.
-/

namespace Reconcile

/-- The compact coherence layer preserves the underlying draft execution
    contract. -/
def draft_finalize_coherence_draft_spec {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : FinalizeCoherenceSpec curHeap curRoot nextHeap nextRoot) :
    DraftExecSpec curHeap curRoot nextHeap nextRoot :=
  spec.draftSpec

/-- Shared finalized-image coherence at the draft layer.

    Implementation-facing reading: if two final positions denote the same
    draft-originating value, finalization must make them point to one grounded
    finalized image in the next graph. -/
theorem draft_shared_finalized_image_coherence {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : FinalizeCoherenceSpec curHeap curRoot nextHeap nextRoot)
    {p₁ p₂ : DraftPath}
    (hShared : spec.sharedOriginAt p₁ p₂) :
    ∃ v, spec.finalValueAt p₁ v ∧ spec.finalValueAt p₂ v :=
  spec.resolutionWitness.sharedImage p₁ p₂ hShared

/-- Moved-reference final-location correctness at the draft layer.

    Implementation-facing reading: if a draft-originating value is moved, the
    old final path must be absent and the new final path must contain a grounded
    finalized value before returning the next graph. -/
theorem draft_moved_reference_final_location_correctness {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : FinalizeCoherenceSpec curHeap curRoot nextHeap nextRoot)
    {pOld pNew : DraftPath}
    (hMove : spec.movedOriginTo pOld pNew) :
    spec.finalValueAbsentAt pOld ∧ ∃ v, spec.finalValueAt pNew v :=
  spec.resolutionWitness.movedImage pOld pNew hMove

/-- Collection-captured-draft finalization correctness at the draft
    layer.

    Implementation-facing reading: if a final collection position captures a
    draft-originating value, finalization must resolve that position to a
    grounded finalized next value before returning the next graph. -/
theorem draft_collection_captured_draft_finalization_correctness
    {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : FinalizeCoherenceSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath}
    (hCaptured : spec.capturedDraftValueAt p) :
    ∃ v, spec.finalValueAt p v :=
  spec.resolutionWitness.capturedImage p hCaptured

end Reconcile
