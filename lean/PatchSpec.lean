/-
  Patch — replacement root semantics under the draft-finalize-then-`reconcile` model.

  This file defines the new patch semantic center as a factorization through:

    DraftExecSpec + ReconcileSpec

  It deliberately avoids the legacy instruction-language patch model.
  This is now the canonical `PatchSpec` module for the draft-finalize-then-
  `reconcile` patch semantics.
-/

import PatchDraftSoundness
import ReconcileSpec

namespace Reconcile

/-- Replacement patch root semantics.

    A patch result is valid when there exists one finalized next graph produced
    by the draft execution layer, and one ordinary reconcile publication from
    the current graph to that next graph. -/
structure PatchSpecCore {A : Type} [AtomEq A]
    (curHeap : Heap A CurId)
    (resultHeap : Heap A ResId)
    (curRoot : Value A CurId)
    (resultRoot : Value A ResId) where
  nextHeap : Heap A NextId
  nextRoot : Value A NextId
  draftSpec : DraftExecSpec curHeap curRoot nextHeap nextRoot
  reconcileSpec : ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot

/-- Thin root packaging for the replacement patch model.
    This is intentionally small: patch root semantics are exactly the existence
    of a valid `PatchSpecCore` witness. -/
def PatchRootSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId)
    (resultHeap : Heap A ResId)
    (curRoot : Value A CurId)
    (resultRoot : Value A ResId) : Prop :=
  Nonempty (PatchSpecCore curHeap resultHeap curRoot resultRoot)

/-- The replacement patch model has an explicit finalized next graph. -/
theorem patch_has_next_graph {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : PatchSpecCore curHeap resultHeap curRoot resultRoot) :
    ∃ nextHeap : Heap A NextId, ∃ nextRoot : Value A NextId,
      Nonempty (DraftExecSpec curHeap curRoot nextHeap nextRoot) ∧
      ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot := by
  exact ⟨spec.nextHeap, spec.nextRoot, ⟨spec.draftSpec⟩, spec.reconcileSpec⟩

/-- Root-return replacement in the draft layer becomes ordinary root reconcile
    publication of the returned replacement value. -/
theorem patch_root_return_replacement {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {v : Value A NextId}
    (hMode : spec.draftSpec.returnMode = .replaced v) :
    spec.nextRoot = v :=
  draft_root_return_replacement spec.draftSpec hMode

/-- The replacement patch root relation is exactly the factorized patch spec. -/
theorem patch_root_iff_patch_spec {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId} :
    PatchRootSpec curHeap resultHeap curRoot resultRoot ↔
      Nonempty (PatchSpecCore curHeap resultHeap curRoot resultRoot) := by
  rfl

end Reconcile
