import RecipePublication.RecipePublicationSpec
import Reconcile.ReconcileSoundness

/-! Caller composition: upstream recipe and capture assumptions plus verified publication. -/

namespace Reconcile

variable {A : Type} [AtomEq A] {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
  {curRoot : Value A CurId} {resultRoot : Value A ResId}

/-- The finalized next graph is faithfully published. -/
theorem recipe_publication_surface_soundness
    (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot) :
    SurfaceEq spec.nextHeap resultHeap spec.nextRoot resultRoot :=
  reconcile_soundness spec.reconcileSpec

/-- Successful object publication retains current even for explicit recipe replacements. -/
theorem recipe_publication_root_retained {cr nr}
    (spec : RecipePublicationSpecCore curHeap resultHeap (.ref cr) resultRoot)
    (hn : spec.nextRoot = .ref nr) : resultRoot = .ref (.inl cr) := by
  apply reconcile_root_retained (nextHeap := spec.nextHeap) (curHeap := curHeap)
  simpa [hn] using spec.reconcileSpec.rootSpec

/-- Explicit replacement is still subject to the reconcile root boundary. -/
theorem recipe_publication_root_replacement_publication
    (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot) {v}
    (hm : spec.draftSpec.returnMode = .replaced v) :
    execReconcileRoot curHeap spec.nextHeap curRoot v = .ok resultRoot := by
  rw [← recipe_publication_root_return_replacement spec hm]
  exact spec.reconcileSpec.rootSpec

/-- No return means ordinary undefined, represented as an atom, not implicit draft return. -/
theorem recipe_publication_root_replaced_atom
    (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot) {a}
    (hm : spec.draftSpec.returnMode = .replaced (.atom a)) : resultRoot = .atom a := by
  have h := recipe_publication_root_replacement_publication spec hm
  rw [reconcile_root_next_atom] at h
  exact (Except.ok.inj h).symm

theorem recipe_publication_no_collapse (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {n₁ n₂} (h₁ : n₁ ∈ spec.nextHeap.keys) (h₂ : n₂ ∈ spec.nextHeap.keys) (hne : n₁ ≠ n₂) :
    spec.reconcileSpec.witness.image n₁ ≠ spec.reconcileSpec.witness.image n₂ :=
  reconcile_no_collapse spec.reconcileSpec.witness h₁ h₂ hne

theorem recipe_publication_sharing (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {n₁ n₂} (he : n₁ = n₂) :
    spec.reconcileSpec.witness.image n₁ = spec.reconcileSpec.witness.image n₂ :=
  reconcile_sharing spec.reconcileSpec.witness he

theorem recipe_publication_cycle_preservation (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {n} (hc : Relation.TransGen (edge spec.nextHeap) n n) :
    Relation.TransGen (edge resultHeap)
      (spec.reconcileSpec.witness.image n) (spec.reconcileSpec.witness.image n) :=
  reconcile_cycle_preservation spec.reconcileSpec hc

/-- Both actual view payloads point to the one selected buffer. -/
theorem recipe_publication_buffer_alias (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    {n₁ n₂ b o₁ o₂ l₁ l₂}
    (h₁ : spec.nextHeap.lookup n₁ = some (.dataView b o₁ l₁))
    (h₂ : spec.nextHeap.lookup n₂ = some (.dataView b o₂ l₂)) :
    resultHeap.lookup (spec.reconcileSpec.witness.image n₁) =
      some (.dataView (spec.reconcileSpec.witness.image b) o₁ l₁) ∧
    resultHeap.lookup (spec.reconcileSpec.witness.image n₂) =
      some (.dataView (spec.reconcileSpec.witness.image b) o₂ l₂) :=
  reconcile_buffer_alias spec.reconcileSpec h₁ h₂

/-- The immutable captured-record theorem can feed caller publication directly.
    Instantiate `finalized` with `Immutable.selected_published`; no global surface
    equality is assumed for either stage. -/
theorem recipe_publication_captured_soundness {I : Type} [DecidableEq I]
    (spec : RecipePublicationSpecCore curHeap resultHeap curRoot resultRoot)
    (captured : Heap A I) (capturedRoot : Value A I)
    (image : I → NextId) (proto : I → ProtoLabel → ProtoLabel)
    (finalized : Published captured spec.nextHeap image proto)
    (hroot : capturedRoot.remap image = spec.nextRoot)
    (hw : HeapWF captured) (hr : RootWF captured capturedRoot) :
    SurfaceEq captured resultHeap capturedRoot resultRoot := by
  have h := (finalized.compose spec.reconcileSpec.published).surface hw capturedRoot hr
  rw [← Value.remap_comp, hroot, spec.reconcileSpec.rootImage] at h
  exact h

end Reconcile
