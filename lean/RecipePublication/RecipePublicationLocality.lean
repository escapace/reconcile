import RecipePublication.RecipePublicationOrder

/-!
# Caller publication: locality

Locality and behavioral corollaries for the draft-finalize-then-`reconcile` model, as
caller-publication wrappers around:

- draft-layer touch locality,
- explicit delete vs assignment-of-undefined,
- retained-root publication locality,
- supported-surface delete and untouched-key corollaries.
-/

namespace Reconcile

/-- Draft touch locality transported to caller publication: untouched regions
    preserved by the finalization witness remain surface-equivalent in the
    finalized next graph. -/
theorem recipe_publication_touch_locality_next {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {c : CurId} {n : NextId}
    (hPres : spec.draftSpec.finalizeWitness.preserve.lookup c = some n)
    (hUntouched : spec.draftSpec.touches.unchangedRegion c) :
    SurfaceEq curHeap spec.nextHeap (.ref c) (.ref n) :=
  draft_untouched_preserved spec.draftSpec hPres hUntouched

/-- Behavioral corollary: explicit delete remains distinct from assignment of
    `undefined` at the composition layer because caller publication factors through draft
    semantics. -/
theorem recipe_publication_delete_is_explicit {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {p : DraftPath}
    (hDel : spec.draftSpec.touches.deletedPathAt p) :
    ¬ spec.draftSpec.touches.assignedUndefinedAt p :=
  draft_delete_is_explicit spec.draftSpec hDel

/-- Behavioral corollary: assigning `undefined` remains an ordinary assignment,
    not deletion, at the composition layer. -/
theorem recipe_publication_undefined_is_ordinary {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {p : DraftPath}
    (hUndef : spec.draftSpec.touches.assignedUndefinedAt p) :
    ¬ spec.draftSpec.touches.deletedPathAt p :=
  draft_undefined_assignment_is_ordinary spec.draftSpec hUndef

/-- Caller-publication untouched-path preservation corollary.

    This is intentionally modest: it states the preserved current→next fact from
    the draft layer, and relies on reconciliation soundness for publication of
    the finalized next graph. It does not overstate a direct current→result
    identity theorem across namespace boundaries. -/
theorem recipe_publication_untouched_path_preservation {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {c : CurId} {n : NextId}
    (hPres : spec.draftSpec.finalizeWitness.preserve.lookup c = some n)
    (hUntouched : spec.draftSpec.touches.unchangedRegion c) :
    SurfaceEq curHeap spec.nextHeap (.ref c) (.ref n) ∧
    SurfaceEq spec.nextHeap resultHeap spec.nextRoot resultRoot :=
  ⟨draft_untouched_preserved spec.draftSpec hPres hUntouched,
    Reconcile.recipe_publication_surface_soundness spec⟩

/-- Supported-surface delete-removes-key theorem for retained plain-object
    roots. If draft execution records deletion of key `k` at the object root,
    then the finalized next object omits `k`, and the retained published result
    omits `k` as well. -/
theorem recipe_publication_delete_removes_key_retained_root {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {cr : CurId} {nr : NextId}
    {pCur : ProtoLabel} {pNext : ProtoLabel}
    {curFields : ObjFields A CurId} {nextFields : ObjFields A NextId}
    (hPath : spec.draftSpec.touches.pathNode [] cr)
    (hPres : spec.draftSpec.finalizeWitness.preserve.lookup cr = some nr)
    (hCur : curHeap.lookup cr = some (.plainObject pCur curFields))
    (hNext : spec.nextHeap.lookup nr = some (.plainObject pNext nextFields))
    (hImage : spec.reconcileSpec.witness.image nr = .inl cr)
    {k : PropertyKey}
    (hDel : spec.draftSpec.touches.deletedPathAt [DraftPathElem.objectKey k]) :
    ∃ rFields : ObjFields A ResId,
      resultHeap.lookup (.inl cr) = some (.plainObject pCur rFields) ∧
      List.dlookup k rFields = none := by
  have hObj := draft_object_effects spec.draftSpec hPath hPres hCur hNext
  have hNextAbsent : List.dlookup k nextFields = none :=
    hObj.deletedKeyAbsent k (by simpa using hDel)
  obtain ⟨rFields, hLookup, hKeys⟩ :=
    Reconcile.recipe_publication_object_order_retained_root spec hCur hNext hImage
  have hAbsentR : List.dlookup k rFields = none := by
    cases hdk : List.dlookup k rFields with
    | none => simp
    | some rv =>
        exfalso
        have hSomeR : (List.dlookup k rFields).isSome := by simp [hdk]
        have hMemR : k ∈ rFields.keys := List.dlookup_isSome.mp hSomeR
        have hMemN : k ∈ nextFields.keys := by simpa [hKeys] using hMemR
        have hSomeN : (List.dlookup k nextFields).isSome := List.dlookup_isSome.mpr hMemN
        rw [hNextAbsent] at hSomeN
        cases hSomeN
  exact ⟨rFields, hLookup, hAbsentR⟩

/-- Supported-surface untouched-key preservation theorem for retained
    plain-object roots. If key `k` is untouched at the root object, it remains
    present in the finalized next object and in the retained published result. -/
theorem recipe_publication_untouched_key_preserved_retained_root {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {cr : CurId} {nr : NextId}
    {pCur : ProtoLabel} {pNext : ProtoLabel}
    {curFields : ObjFields A CurId} {nextFields : ObjFields A NextId}
    (hPath : spec.draftSpec.touches.pathNode [] cr)
    (hPres : spec.draftSpec.finalizeWitness.preserve.lookup cr = some nr)
    (hCur : curHeap.lookup cr = some (.plainObject pCur curFields))
    (hNext : spec.nextHeap.lookup nr = some (.plainObject pNext nextFields))
    (hImage : spec.reconcileSpec.witness.image nr = .inl cr)
    {k : PropertyKey} {cv : Value A CurId}
    (hCurKey : List.dlookup k curFields = some cv)
    (hUntouched : spec.draftSpec.touches.unchangedPath [DraftPathElem.objectKey k]) :
    ∃ nv : Value A NextId, ∃ rv : Value A ResId, ∃ rFields : ObjFields A ResId,
      resultHeap.lookup (.inl cr) = some (.plainObject pCur rFields) ∧
      List.dlookup k nextFields = some nv ∧
      SurfaceEq curHeap spec.nextHeap cv nv ∧
      List.dlookup k rFields = some rv := by
  have hObj := draft_object_effects spec.draftSpec hPath hPres hCur hNext
  obtain ⟨nv, hNextKey, hEq⟩ := hObj.untouchedKeyPreserved k cv hCurKey (by simpa using hUntouched)
  obtain ⟨rFields, hLookup, hKeys⟩ :=
    Reconcile.recipe_publication_object_order_retained_root spec hCur hNext hImage
  have hMem : k ∈ nextFields.keys := List.dlookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨nv, hNextKey⟩)
  have hMemR : k ∈ rFields.keys := by simpa [hKeys] using hMem
  obtain ⟨rv, hRKey⟩ := Option.isSome_iff_exists.mp (List.dlookup_isSome.mpr hMemR)
  exact ⟨nv, rv, rFields, hLookup, hNextKey, hEq, hRKey⟩

end Reconcile
