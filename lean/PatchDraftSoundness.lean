/-
  Patch draft layer — theorem projections.

  This file records the first theorem tranche for the proof-facing draft
  semantics. As with the existing runtime proof tree, these theorems mostly
  expose the intended semantic obligations from the central specification.
-/

import PatchDraftSpec

namespace Reconcile

/-- D1 — Lazy child-draft creation: child drafts only exist at accessed paths. -/
theorem draft_lazy_child_creation {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath}
    (hChild : spec.touches.childDraftAt p) :
    spec.touches.accessed p :=
  spec.lazyChildDrafts p hChild

/-- D2 — Read non-interference: pure reads do not directly mark the denoted
    current node modified or copied. -/
theorem draft_read_non_interference {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath} {c : CurId}
    (hRead : spec.touches.pureReadAt p)
    (hNode : spec.touches.pathNode p c) :
    ¬ spec.touches.modifiedNode c ∧ ¬ spec.touches.copiedNode c :=
  spec.readNonInterference p c hRead hNode

/-- D3 — Copy-on-write allocation: copied and modified coincide in the abstract
    draft node bookkeeping. -/
theorem draft_copy_on_write {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {c : CurId} :
    spec.touches.copiedNode c ↔ spec.touches.modifiedNode c :=
  spec.copyOnWrite c

/-- D4 — Parent-chain modification propagation. -/
theorem draft_parent_modification_propagates {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {c p : CurId}
    (hPar : spec.touches.parentOf c p)
    (hMod : spec.touches.modifiedNode c) :
    spec.touches.modifiedNode p :=
  spec.parentPropagation c p hPar hMod

/-- D5 — Explicit delete is distinct from assignment of `undefined`. -/
theorem draft_delete_is_explicit {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath}
    (hDel : spec.touches.deletedPathAt p) :
    ¬ spec.touches.assignedUndefinedAt p :=
  spec.deleteNotUndefinedAssign p hDel

/-- D5 — Assignment of `undefined` is not deletion. -/
theorem draft_undefined_assignment_is_ordinary {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath}
    (hUndef : spec.touches.assignedUndefinedAt p) :
    ¬ spec.touches.deletedPathAt p :=
  spec.undefinedAssignNotDelete p hUndef

/-- D6 — Finalization produces one next graph, represented by the next heap and
    root together with their well-formedness obligations. -/
theorem draft_finalize_produces_next_graph {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot) :
    HeapWF nextHeap ∧ RootWF nextHeap nextRoot :=
  ⟨spec.nextHeapWF, spec.nextRootWF⟩

/-- Object effects are captured by the finalized-object contract. -/
theorem draft_object_effects {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath} {c : CurId} {n : NextId}
    {pCur : ProtoLabel} {pNext : ProtoLabel}
    {curFields : ObjFields A CurId}
    {nextFields : ObjFields A NextId}
    (hPath : spec.touches.pathNode p c)
    (hPres : spec.finalizeWitness.preserve.lookup c = some n)
    (hCur : curHeap.lookup c = some (.plainObject pCur curFields))
    (hNext : nextHeap.lookup n = some (.plainObject pNext nextFields)) :
    ObjectDraftNodeSpec curHeap nextHeap spec.touches p curFields nextFields :=
  spec.objectEffects p c n pCur pNext curFields nextFields hPath hPres hCur hNext

/-- D7 — Untouched preserved regions are surface-equivalent across the
    finalization witness. -/
theorem draft_untouched_preserved {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {c : CurId} {n : NextId}
    (hPres : spec.finalizeWitness.preserve.lookup c = some n)
    (hUntouched : ¬ spec.touches.touchedNode c) :
    SurfaceEq curHeap nextHeap (.ref c) (.ref n) :=
  spec.untouchedPreserved c n hPres hUntouched

/-- D8-array — Array effects are captured by the finalized-array contract. -/
theorem draft_array_effects {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath} {c : CurId} {n : NextId}
    {curEntries : List (Option (Value A CurId))}
    {nextEntries : List (Option (Value A NextId))}
    (hPath : spec.touches.pathNode p c)
    (hPres : spec.finalizeWitness.preserve.lookup c = some n)
    (hCur : curHeap.lookup c = some (.array curEntries))
    (hNext : nextHeap.lookup n = some (.array nextEntries)) :
    ∃ _ : ArrayDraftNodeSpec curHeap nextHeap spec.touches p curEntries nextEntries, True := by
  exact ⟨spec.arrayEffects p c n curEntries nextEntries hPath hPres hCur hNext, trivial⟩

/-- D8-map — Map effects are captured by the finalized-map contract. -/
theorem draft_map_effects {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath} {c : CurId} {n : NextId}
    {curEntries : List (Value A CurId × Value A CurId)}
    {nextEntries : List (Value A NextId × Value A NextId)}
    (hPath : spec.touches.pathNode p c)
    (hPres : spec.finalizeWitness.preserve.lookup c = some n)
    (hCur : curHeap.lookup c = some (.map curEntries))
    (hNext : nextHeap.lookup n = some (.map nextEntries)) :
    ∃ _ : MapDraftNodeSpec spec.touches p nextEntries, True := by
  exact ⟨spec.mapEffects p c n curEntries nextEntries hPath hPres hCur hNext, trivial⟩

/-- D8-set — Set effects are captured by the finalized-set contract. -/
theorem draft_set_effects {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {p : DraftPath} {c : CurId} {n : NextId}
    {curValues : List (Value A CurId)}
    {nextValues : List (Value A NextId)}
    (hPath : spec.touches.pathNode p c)
    (hPres : spec.finalizeWitness.preserve.lookup c = some n)
    (hCur : curHeap.lookup c = some (.set curValues))
    (hNext : nextHeap.lookup n = some (.set nextValues)) :
    ∃ _ : SetDraftNodeSpec spec.touches p nextValues, True := by
  exact ⟨spec.setEffects p c n curValues nextValues hPath hPres hCur hNext, trivial⟩

/-- D9 — Explicit root replacement: if the draft execution mode is replacement,
    the returned replacement value is the finalized next root. -/
theorem draft_root_return_replacement {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {curRoot : Value A CurId}
    {nextHeap : Heap A NextId} {nextRoot : Value A NextId}
    (spec : DraftExecSpec curHeap curRoot nextHeap nextRoot)
    {v : Value A NextId}
    (hMode : spec.returnMode = .replaced v) :
    nextRoot = v := by
  cases hret : spec.returnMode with
  | finalized =>
      simp [hret] at hMode
  | replaced v' =>
      have hv : v' = v := by simpa [hret] using hMode
      subst hv
      simpa [hret] using spec.returnModeSpec

end Reconcile
