import ReconcileSpec

namespace Reconcile

variable {A : Type} {curHeap : Heap A CurId} {nextHeap : Heap A NextId}
  {resultHeap : Heap A ResId} {curRoot : Value A CurId} {nextRoot : Value A NextId}
  {resultRoot : Value A ResId}

/-- Object/object success returns the existing root, never a detached replacement. -/
theorem reconcile_root_retained {cr nr}
    (h : execReconcileRoot curHeap nextHeap (.ref cr) (.ref nr) = .ok resultRoot) :
    resultRoot = .ref (.inl cr) := by
  simp only [execReconcileRoot] at h
  split at h <;> (try split at h) <;> simp_all

/-- The non-object boundary returns the requested value directly. -/
theorem reconcile_root_cur_atom (a : A) (next : Value A NextId) :
    execReconcileRoot curHeap nextHeap (.atom a) next = .ok (nextRootImage next) := rfl

theorem reconcile_root_next_atom (cur : Value A CurId) (a : A) :
    execReconcileRoot curHeap nextHeap cur (.atom a) = .ok (.atom a) := by
  cases cur <;> rfl

/-- Different binary extents are impossible at a fixed buffer root. -/
theorem reconcile_buffer_root_error {cr nr} {cb nb : List UInt8}
    (hc : curHeap.lookup cr = some (.arrayBuffer cb))
    (hn : nextHeap.lookup nr = some (.arrayBuffer nb)) (hne : cb.length ≠ nb.length) :
    execReconcileRoot curHeap nextHeap (.ref cr) (.ref nr) = .error .incompatibleRoot := by
  simp [execReconcileRoot, hc, hn, compatibleShape, hne]

/-- Soundness is derived by finite-depth induction in `Published.surface`. -/
theorem reconcile_soundness [AtomEq A]
    (spec : ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot) :
    SurfaceEq nextHeap resultHeap nextRoot resultRoot := by
  rw [← spec.rootImage]
  exact spec.published.surface spec.nextWF nextRoot spec.nextRootWF

/-- An actual selected image cannot collapse distinct captured nodes. -/
theorem reconcile_no_collapse (w : ReconcileWitness curHeap nextHeap)
    {n₁ n₂} (h₁ : n₁ ∈ nextHeap.keys) (h₂ : n₂ ∈ nextHeap.keys) (hne : n₁ ≠ n₂) :
    w.image n₁ ≠ w.image n₂ := by
  intro he
  exact hne (w.storageDistinct n₁ h₁ n₂ h₂ (congrArg w.storage he))

/-- Two incoming references to one node use the same selected identity. -/
theorem reconcile_sharing (w : ReconcileWitness curHeap nextHeap) {n₁ n₂}
    (he : n₁ = n₂) : w.image n₁ = w.image n₂ := congrArg w.image he

/-- Cycles are derived from the actual payloads associated with this witness. -/
theorem reconcile_cycle_preservation
    (spec : ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot) {n}
    (hc : Relation.TransGen (edge nextHeap) n n) :
    Relation.TransGen (edge resultHeap) (spec.witness.image n) (spec.witness.image n) :=
  spec.published.path hc

/-- Ordered fields and their values are published at the selected identity. -/
theorem reconcile_object_payload
    (spec : ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot)
    {n p fs} (hn : nextHeap.lookup n = some (.plainObject p fs)) :
    resultHeap.lookup (spec.witness.image n) =
      some (.plainObject (publicationProto curHeap spec.witness.image n p)
        (remapFields spec.witness.image fs)) := spec.published n _ hn

/-- A shared next buffer remains the same buffer edge in both published views. -/
theorem reconcile_buffer_alias
    (spec : ReconcileSpec curHeap nextHeap resultHeap curRoot nextRoot resultRoot)
    {n₁ n₂ b o₁ o₂ l₁ l₂}
    (h₁ : nextHeap.lookup n₁ = some (.dataView b o₁ l₁))
    (h₂ : nextHeap.lookup n₂ = some (.dataView b o₂ l₂)) :
    resultHeap.lookup (spec.witness.image n₁) = some (.dataView (spec.witness.image b) o₁ l₁) ∧
    resultHeap.lookup (spec.witness.image n₂) = some (.dataView (spec.witness.image b) o₂ l₂) :=
  ⟨spec.published n₁ _ h₁, spec.published n₂ _ h₂⟩

end Reconcile
