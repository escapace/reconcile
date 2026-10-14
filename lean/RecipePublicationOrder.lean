/- Exact payload corollaries for the selected caller-publication image. -/
import RecipePublicationSoundness

namespace Reconcile

variable {A : Type} [AtomEq A] {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
  {curRoot : Value A CurId} {resultRoot : Value A ResId}

/-- The selected identity must be tied to this node, not an arbitrary witness or root. -/
theorem recipe_publication_object_order_retained_root
    (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {cr nr pCur pNext cFields nFields}
    (hCur : curHeap.lookup cr = some (.plainObject pCur cFields))
    (hNext : spec.nextHeap.lookup nr = some (.plainObject pNext nFields))
    (hImage : spec.reconcileSpec.witness.image nr = .inl cr) :
    ∃ rFields : ObjFields A ResId,
      resultHeap.lookup (.inl cr) = some (.plainObject pCur rFields) ∧
      rFields.keys = nFields.keys := by
  refine ⟨remapFields spec.reconcileSpec.witness.image nFields, ?_, remapFields_keys _ _⟩
  have h := reconcile_object_payload spec.reconcileSpec hNext
  change resultHeap.lookup (spec.reconcileSpec.witness.image nr) = _ at h
  rw [hImage] at h
  simpa [publicationProto, hImage, hCur] using h

/-- Array shape and every hole/present value follow from the exact mapped payload. -/
theorem recipe_publication_array_shape (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {n es} (hn : spec.nextHeap.lookup n = some (.array es)) :
    resultHeap.lookup (spec.reconcileSpec.witness.image n) =
      some (.array (es.map (Option.map (Value.remap spec.reconcileSpec.witness.image)))) :=
  spec.reconcileSpec.published n _ hn

omit [AtomEq A] in
/-- Mapping does not confuse holes with any atom, including undefined. -/
theorem recipe_publication_array_hole_vs_present (image : NextId → ResId)
    (slot : Option (Value A NextId)) :
    slot.map (Value.remap image) = none ↔ slot = none := by cases slot <;> simp

/-- Ordered map entries preserve both key and value identity at each ordinal. -/
theorem recipe_publication_map_order (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {n es} (hn : spec.nextHeap.lookup n = some (.map es)) :
    resultHeap.lookup (spec.reconcileSpec.witness.image n) = some (.map
      (es.map fun (k, v) =>
        (k.remap spec.reconcileSpec.witness.image, v.remap spec.reconcileSpec.witness.image))) :=
  spec.reconcileSpec.published n _ hn

theorem recipe_publication_set_order (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {n vs} (hn : spec.nextHeap.lookup n = some (.set vs)) :
    resultHeap.lookup (spec.reconcileSpec.witness.image n) =
      some (.set (vs.map (Value.remap spec.reconcileSpec.witness.image))) :=
  spec.reconcileSpec.published n _ hn

end Reconcile
