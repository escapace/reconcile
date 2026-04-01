/-
  Patch — order and shape theorems for the replacement draft-finalize-then-
  `reconcile` model.

  These theorems are the patch-level transport layer for object own-key order,
  array shape, map ordinal order, and set ordinal order.

  They intentionally reuse the non-legacy reconcile extraction lemmas proved in
  `lean/ReconcileSoundness.lean`.
-/

import PatchSoundness

namespace Reconcile

/-- O1 — Object own-key order theorem, transported through the replacement
    patch model for retained plain-object roots.

    This theorem is intentionally retained-root scoped: it matches the current
    `ReconcileSpec.nodeSpec` interface, which exposes node-shape facts exactly
    at retained roots. -/
theorem patch_object_order_retained_root {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {w : ReconcileWitness} (_hw : WitnessInv w)
    {cr : CurId} {nr : NextId}
    {pCur : ProtoLabel} {pNext : ProtoLabel}
    {cFields : ObjFields A CurId} {nFields : ObjFields A NextId}
    (hCur : curHeap.lookup cr = some (.plainObject pCur cFields))
    (hNext : spec.nextHeap.lookup nr = some (.plainObject pNext nFields))
    (hKind : (Node.plainObject pCur cFields).kind = (Node.plainObject pNext nFields).kind)
    (hRet : resultRoot = .ref (.inl cr)) :
    ∃ rFields : ObjFields A ResId,
      resultHeap.lookup (.inl cr) = some (.plainObject pCur rFields) ∧
      rFields.keys = nFields.keys := by
  obtain ⟨rnd, hlookup, hnode⟩ := spec.reconcileSpec.nodeSpec w cr nr
    (.plainObject pCur cFields) (.plainObject pNext nFields) hCur hNext hKind hRet
  cases hnode with
  | plainObject hkeys _ =>
      exact ⟨_, hlookup, hkeys⟩

/-- O2 — Array shape/order theorem, transported through the replacement patch
    model for retained array roots. -/
theorem patch_array_shape_retained_root {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {w : ReconcileWitness} (_hw : WitnessInv w)
    {cr : CurId} {nr : NextId}
    {ce : List (Option (Value A CurId))}
    {ne : List (Option (Value A NextId))}
    (hCur : curHeap.lookup cr = some (.array ce))
    (hNext : spec.nextHeap.lookup nr = some (.array ne))
    (hKind : (Node.array ce).kind = (Node.array ne).kind)
    (hRet : resultRoot = .ref (.inl cr)) :
    ∃ re : List (Option (Value A ResId)),
      resultHeap.lookup (.inl cr) = some (.array re) ∧
      re.length = ne.length ∧
      (∀ i (hi_n : i < ne.length) (hi_r : i < re.length),
        match ne[i] with
        | none => re[i] = none
        | some nv => ∃ rv, re[i] = some rv ∧ ReconciledChild curHeap spec.nextHeap w nv rv) := by
  obtain ⟨rnd, hlookup, hnode⟩ := spec.reconcileSpec.nodeSpec w cr nr
    (.array ce) (.array ne) hCur hNext hKind hRet
  cases hnode with
  | array hlen hpts =>
      exact ⟨_, hlookup, hlen, hpts⟩

/-- Explicit patch-level hole-vs-present-slot corollary for retained array
    roots. This is the theorem-facing form of the semantic distinction between
    holes and present values, including ordinary values such as `undefined`. -/
theorem patch_array_hole_vs_present_retained_root {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {w : ReconcileWitness} (hw : WitnessInv w)
    {cr : CurId} {nr : NextId}
    {ce : List (Option (Value A CurId))}
    {ne : List (Option (Value A NextId))}
    (hCur : curHeap.lookup cr = some (.array ce))
    (hNext : spec.nextHeap.lookup nr = some (.array ne))
    (hKind : (Node.array ce).kind = (Node.array ne).kind)
    (hRet : resultRoot = .ref (.inl cr))
    {i : Nat} (hi_n : i < ne.length) :
    ∃ re : List (Option (Value A ResId)),
      resultHeap.lookup (.inl cr) = some (.array re) ∧
      ∃ hi_r : i < re.length,
        ((ne[i]'hi_n = none → re[i]'hi_r = none) ∧
         (∀ nv, ne[i]'hi_n = some nv → ∃ rv, re[i]'hi_r = some rv ∧ ReconciledChild curHeap spec.nextHeap w nv rv)) := by
  obtain ⟨re, hlookup, hlen, hpts⟩ :=
    Reconcile.patch_array_shape_retained_root spec (w := w) hw hCur hNext hKind hRet
  have hi_r : i < re.length := by simpa [hlen] using hi_n
  refine ⟨re, hlookup, hi_r, ?_⟩
  constructor
  · intro hHole
    have hstep := hpts i hi_n hi_r
    rw [show ne[i] = none from hHole] at hstep
    exact hstep
  · intro nv hPresent
    have hstep := hpts i hi_n hi_r
    rw [show ne[i] = some nv from hPresent] at hstep
    exact hstep

/-- O3 — Map insertion-order theorem, transported through the replacement
    patch model for retained map roots. -/
theorem patch_map_order_retained_root {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {w : ReconcileWitness} (_hw : WitnessInv w)
    {cr : CurId} {nr : NextId}
    {ce : List (Value A CurId × Value A CurId)}
    {ne : List (Value A NextId × Value A NextId)}
    (hCur : curHeap.lookup cr = some (.map ce))
    (hNext : spec.nextHeap.lookup nr = some (.map ne))
    (hKind : (Node.map ce).kind = (Node.map ne).kind)
    (hRet : resultRoot = .ref (.inl cr)) :
    ∃ re : List (Value A ResId × Value A ResId),
      resultHeap.lookup (.inl cr) = some (.map re) ∧
      re.length = ne.length ∧
      (∀ i (hi_n : i < ne.length) (hi_r : i < re.length),
        ReconciledChild curHeap spec.nextHeap w (ne[i]).1 (re[i]).1 ∧
        ReconciledChild curHeap spec.nextHeap w (ne[i]).2 (re[i]).2) := by
  obtain ⟨rnd, hlookup, hnode⟩ := spec.reconcileSpec.nodeSpec w cr nr
    (.map ce) (.map ne) hCur hNext hKind hRet
  cases hnode with
  | map hlen hpts =>
      exact ⟨_, hlookup, hlen, hpts⟩

/-- O4 — Set insertion-order theorem, transported through the replacement
    patch model for retained set roots. -/
theorem patch_set_order_retained_root {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {resultHeap : Heap A ResId}
    {curRoot : Value A CurId} {resultRoot : Value A ResId}
    (spec : Reconcile.PatchSpecCore curHeap resultHeap curRoot resultRoot)
    {w : ReconcileWitness} (_hw : WitnessInv w)
    {cr : CurId} {nr : NextId}
    {cv : List (Value A CurId)}
    {nv : List (Value A NextId)}
    (hCur : curHeap.lookup cr = some (.set cv))
    (hNext : spec.nextHeap.lookup nr = some (.set nv))
    (hKind : (Node.set cv).kind = (Node.set nv).kind)
    (hRet : resultRoot = .ref (.inl cr)) :
    ∃ rv : List (Value A ResId),
      resultHeap.lookup (.inl cr) = some (.set rv) ∧
      rv.length = nv.length ∧
      (∀ i (hi_n : i < nv.length) (hi_r : i < rv.length),
        ReconciledChild curHeap spec.nextHeap w nv[i] rv[i]) := by
  obtain ⟨rnd, hlookup, hnode⟩ := spec.reconcileSpec.nodeSpec w cr nr
    (.set cv) (.set nv) hCur hNext hKind hRet
  cases hnode with
  | set hlen hpts =>
      exact ⟨_, hlookup, hlen, hpts⟩

end Reconcile
