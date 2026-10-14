/-
  Caller composition — `reconcile(current, produce(current, recipe))`.

  DraftExecSpec supplies the finalized next graph; ReconcileSpec certifies its
  publication into the current graph.
-/

import ProduceSoundness
import ReconcileSpec

namespace Reconcile

/-- Root semantics of explicit recipe production followed by reconciliation.

    A composition result is valid when there exists one finalized next graph produced
    by the draft execution layer, and one ordinary reconcile publication from
    the current graph to that next graph. -/
structure RecipePublicationSpecCore {A : Type} [AtomEq A]
    (curHeap : Heap A CurId)
    (resultHeap : Heap A ResId)
    (curRoot : Value A CurId)
    (resultRoot : Value A ResId) where
  nextHeap : Heap A NextId
  nextRoot : Value A NextId
  draftSpec : DraftExecSpec curHeap curRoot nextHeap nextRoot
  reconcileSpec : ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot

/-- Thin root packaging for caller publication.
    Its semantics are exactly the existence
    of a valid `RecipePublicationSpecCore` witness. -/
def RecipePublicationRootSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId)
    (resultHeap : Heap A ResId)
    (curRoot : Value A CurId)
    (resultRoot : Value A ResId) : Prop :=
  Nonempty (RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)

/-- Caller publication has an explicit intermediate finalized next graph. -/
theorem recipe_publication_has_next_graph {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot) :
    ∃ nextHeap : Heap A NextId, ∃ nextRoot : Value A NextId,
      Nonempty (DraftExecSpec curHeap curRoot nextHeap nextRoot) ∧
      Nonempty (ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot) := by
  exact ⟨spec.nextHeap, spec.nextRoot, ⟨spec.draftSpec⟩, ⟨spec.reconcileSpec⟩⟩

/-- Root-return replacement in the draft layer becomes ordinary root reconcile
    publication of the returned replacement value. -/
theorem recipe_publication_root_return_replacement {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {v : Value A NextId}
    (hMode : spec.draftSpec.returnMode = .replaced v) :
    spec.nextRoot = v :=
  draft_root_return_replacement spec.draftSpec hMode

/-- The caller-publication root relation is exactly its factorized spec. -/
theorem recipe_publication_root_iff_recipe_publication_spec {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId} :
    RecipePublicationRootSpec curHeap resultHeap curRoot resultRoot ↔
      Nonempty (RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot) := by
  rfl

end Reconcile
