/-
  Patch — soundness and topology for the replacement draft-finalize-then-
  `reconcile` model.

  This file proves the patch-level corollaries that follow directly from the
  new factorization:

    DraftExecSpec + ReconcileSpec

  It intentionally reuses the non-legacy reconcile theorem base.
-/

import PatchSpec
import ReconcileSoundness

namespace Reconcile

/-- Patch-level packaging of the replacement publication witness and its main
    topology consequences. This is the theorem-facing bundle that replaces the
    earlier API shape requiring callers to supply an arbitrary witness by hand. -/
structure PatchTopology where
  witness : ReconcileWitness
  witnessInv : WitnessInv witness

/-- Extract the patch-level topology bundle directly from `PatchSpecCore`. -/
noncomputable def patch_topology_bundle {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot) :
    PatchTopology := by
  classical
  exact Classical.choice <| by
    rcases spec.reconcileSpec.witness with ⟨w, hw⟩
    exact ⟨⟨w, hw⟩⟩

/-- P1 — Patch surface soundness: the patch result is surface-equivalent to the
    finalized next graph produced by draft execution. -/
theorem patch_surface_soundness {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot) :
    SurfaceEq spec.nextHeap resultHeap spec.nextRoot resultRoot :=
  spec.reconcileSpec.surfaceEq

/-- P2 — Patch root fast-path corollary: if draft execution yields the same
    atom at the root, patch inherits reconcile's atom fast path. -/
theorem patch_root_fastpath_atom {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {a : A} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap (.atom a) resultRoot)
    (hNext : spec.nextRoot = .atom a) :
    resultRoot = .atom a := by
  have hroot : ReconcileRootSpec curHeap spec.nextHeap (.atom a) (.atom a) resultRoot := by
    simpa [hNext] using spec.reconcileSpec.rootSpec
  cases hroot with
  | sameAtom => rfl
  | diffAtom hneq =>
      have : False := hneq (AtomEq.eq_refl a)
      exact False.elim this

/-- P3 — Root-return replacement corollary: explicit draft-layer replacement
    becomes ordinary root reconcile publication of that replacement root. -/
theorem patch_root_replacement_publication {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {v : Value A NextId}
    (hMode : spec.draftSpec.returnMode = .replaced v) :
    ReconcileRootSpec curHeap spec.nextHeap curRoot v resultRoot := by
  have hNext : spec.nextRoot = v := Reconcile.patch_root_return_replacement spec hMode
  subst hNext
  exact spec.reconcileSpec.rootSpec

/-- Root-return replacement via an atom collapses to that returned atom at the
    patch result root. -/
theorem patch_root_replaced_atom {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {a : A}
    (hMode : spec.draftSpec.returnMode = .replaced (.atom a)) :
    resultRoot = .atom a := by
  have hpub : ReconcileRootSpec curHeap spec.nextHeap curRoot (.atom a) resultRoot :=
    Reconcile.patch_root_replacement_publication spec hMode
  cases hpub with
  | sameAtom => rfl
  | diffAtom _ => rfl
  | curRefNextAtom => rfl

/-- Root-return replacement via a next ref has exactly the ordinary reconcile
    root outcomes: either direct next-root image under replacement branches, or
    retained current-root identity under the same-kind retained branch. -/
theorem patch_root_replaced_ref_cases {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {nr : NextId}
    (hMode : spec.draftSpec.returnMode = .replaced (.ref nr)) :
    resultRoot = nextRootImage (.ref nr) ∨ ∃ cr : CurId, resultRoot = .ref (.inl cr) := by
  have hpub : ReconcileRootSpec curHeap spec.nextHeap curRoot (.ref nr) resultRoot :=
    Reconcile.patch_root_replacement_publication spec hMode
  cases hpub with
  | curAtomNextRef => exact Or.inl rfl
  | kindMismatch _ _ _ => exact Or.inl rfl
  | refNotFound _ => exact Or.inl rfl
  | sameKind => exact Or.inr ⟨_, rfl⟩

/-- T1 — One-witness patch publication: patch publication is governed by one
    reconcile witness over the finalized next graph and result graph. -/
theorem patch_has_witness {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot) :
    ∃ w : ReconcileWitness, WitnessInv w :=
  spec.reconcileSpec.witness

/-- T1/T2/T3/T4 bundle — patch publication exposes one witness together with
    its main topology consequences. -/
theorem patch_topology_package {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot) :
    ∃ w : ReconcileWitness,
      WitnessInv w ∧
      (∀ n r₁ r₂, w.image.lookup n = some r₁ → w.image.lookup n = some r₂ → r₁ = r₂) ∧
      (∀ n₁ n₂ r₁ r₂, n₁ ≠ n₂ → w.image.lookup n₁ = some r₁ → w.image.lookup n₂ = some r₂ → r₁ ≠ r₂) ∧
      (∀ c₁ c₂ n, w.reuse.lookup c₁ = some n → w.reuse.lookup c₂ = some n → c₁ = c₂) ∧
      (∀ n c, w.image.lookup n = some (.inl c) → w.reuse.lookup c = some n) := by
  rcases spec.reconcileSpec.witness with ⟨w, hw⟩
  exact ⟨w, hw,
    (fun n r₁ r₂ h₁ h₂ => reconcile_sharing hw h₁ h₂),
    (fun n₁ n₂ r₁ r₂ hne h₁ h₂ => reconcile_no_collapse hw hne h₁ h₂),
    (fun c₁ c₂ n h₁ h₂ => reconcile_current_injectivity hw h₁ h₂),
    hw.imageReuseConsist⟩

/-- T2 — Patch-wide sharing preservation, stated directly from `PatchSpecCore`. -/
theorem patch_sharing {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {n : NextId} :
    ∃ w : ReconcileWitness,
      WitnessInv w ∧
      (∀ r₁ r₂, w.image.lookup n = some r₁ → w.image.lookup n = some r₂ → r₁ = r₂) := by
  rcases spec.reconcileSpec.witness with ⟨w, hw⟩
  exact ⟨w, hw, fun r₁ r₂ h₁ h₂ => reconcile_sharing hw h₁ h₂⟩

/-- T3 — Patch-wide no-collapse, stated directly from `PatchSpecCore`. -/
theorem patch_no_collapse {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {n₁ n₂ : NextId}
    (hne : n₁ ≠ n₂) :
    ∃ w : ReconcileWitness,
      WitnessInv w ∧
      (∀ r₁ r₂, w.image.lookup n₁ = some r₁ → w.image.lookup n₂ = some r₂ → r₁ ≠ r₂) := by
  rcases spec.reconcileSpec.witness with ⟨w, hw⟩
  exact ⟨w, hw, fun r₁ r₂ h₁ h₂ => reconcile_no_collapse hw hne h₁ h₂⟩

/-- T4 — Patch-wide current-node injectivity, stated directly from `PatchSpecCore`. -/
theorem patch_current_injectivity {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {n : NextId} :
    ∃ w : ReconcileWitness,
      WitnessInv w ∧
      (∀ c₁ c₂, w.reuse.lookup c₁ = some n → w.reuse.lookup c₂ = some n → c₁ = c₂) := by
  rcases spec.reconcileSpec.witness with ⟨w, hw⟩
  exact ⟨w, hw, fun c₁ c₂ h₁ h₂ => reconcile_current_injectivity hw h₁ h₂⟩

/-- T5 — Direct closed patch cycle theorem.

    Because patch publication factors through one `ReconcileSpec`, any next-node
    cycle in the finalized next graph is preserved at the corresponding result
    image supplied by the patch publication witness. -/
theorem patch_cycle_preservation {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {nr : NextId} {ri : ResId}
    (hcycle : Relation.TransGen (edge spec.nextHeap) nr nr) :
    ∃ w : ReconcileWitness,
      WitnessInv w ∧
      (w.image.lookup nr = some ri →
        Relation.TransGen (edge resultHeap) ri ri) := by
  rcases spec.reconcileSpec.witness with ⟨w, hw⟩
  exact ⟨w, hw, fun himg => reconcile_cycle_preservation spec.reconcileSpec himg hcycle⟩

/-- T6 — Patch-wide buffer/view alias preservation. -/
theorem patch_buffer_alias {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {nb : NextId} :
    ∃ w : ReconcileWitness,
      WitnessInv w ∧
      (∀ r₁ r₂, w.image.lookup nb = some r₁ → w.image.lookup nb = some r₂ → r₁ = r₂) := by
  rcases spec.reconcileSpec.witness with ⟨w, hw⟩
  exact ⟨w, hw, fun r₁ r₂ h₁ h₂ => reconcile_buffer_alias hw h₁ h₂⟩

end Reconcile
