/-
  Reconcile — relational specification of reconcile (Iteration 5).

  Defines the relational semantics of reconcile using witness maps.
  All definitions are non-executable. The executable algorithm comes later.

  Key types:
    - ReconcileWitness: reuse + image witness maps
    - WitnessInv: invariants on witness maps (§5.1)
    - ReconcileRootSpec: root rule (§5.2)
    - ReconcileValueSpec: recursive rule (§5.3)
    - SharedObjectSpec: shared-object fast path (§5.4)
    - ReconcileEntrySpec: entry rule (§5.5)
-/

import Defs
import WF
import SnapshotSpec

namespace Reconcile

/-! ## Reconcile witness state -/

/-- Witness maps for a reconcile operation. -/
structure ReconcileWitness where
  /-- Reuse map: current → next alignment witness. -/
  reuse : ReuseMap
  /-- Image map: next → result id witness. -/
  image : ImageMap

/-! ## Witness invariants (§5.1) -/

/-- The witness maps satisfy the required invariants from §5.1. -/
structure WitnessInv (w : ReconcileWitness) : Prop where
  /-- reuse is injective: one current node consumed for at most one next node. -/
  reuseInj : ∀ c₁ c₂ n,
    w.reuse.lookup c₁ = some n → w.reuse.lookup c₂ = some n → c₁ = c₂
  /-- image is functional (follows from Finmap). -/
  imageFun : ∀ n r₁ r₂,
    w.image.lookup n = some r₁ → w.image.lookup n = some r₂ → r₁ = r₂
  /-- If image(n) = inl c (current reused), then reuse(c) = n. -/
  imageReuseConsist : ∀ n c,
    w.image.lookup n = some (.inl c) → w.reuse.lookup c = some n
  /-- Distinct next nodes have distinct result images (no-collapse). -/
  noCollapse : ∀ n₁ n₂,
    n₁ ≠ n₂ →
    ∀ r₁ r₂, w.image.lookup n₁ = some r₁ → w.image.lookup n₂ = some r₂ →
    r₁ ≠ r₂

/-! ## Root rule (§5.2) -/

/-- Canonical result-namespace image of a next root value.
    This is how the Lean model represents JavaScript-level root branches
    that "return next directly": atoms stay unchanged, while next refs are
    re-expressed in the fresh result namespace. -/
def nextRootImage {A : Type} : Value A NextId → Value A ResId
  | .atom a => .atom a
  | .ref nr => .ref (.inr ⟨nr.val⟩)

/-- The root reconciliation rule. This is the public entry point.
    Returns either the current value unchanged (fast path), the canonical
    result-namespace image of `next` (mismatch branches), or delegates to
    kind-specific reconciliation.

    Result values use `ResId = CurId ⊕ FreshId`:
    - `.inl c` means the current node `c` is retained
    - `.inr f` means a fresh node was allocated -/
inductive ReconcileRootSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId) :
    Value A CurId → Value A NextId → Value A ResId → Prop where
  /-- SameValue atom fast path: return current. -/
  | sameAtom {a : A} :
      ReconcileRootSpec curHeap nextHeap (.atom a) (.atom a) (.atom a)
  /-- Different atoms: return next (current is not object-like). -/
  | diffAtom {a₁ a₂ : A} :
      ¬ AtomEq.eq a₁ a₂ →
      ReconcileRootSpec curHeap nextHeap (.atom a₁) (.atom a₂) (.atom a₂)
  /-- Current is atom, next is ref: return next directly.
      At root level, this means the next value replaces current. -/
  | curAtomNextRef {a : A} {nr : NextId} :
      ReconcileRootSpec curHeap nextHeap (.atom a) (.ref nr)
        (nextRootImage (.ref nr))
  /-- Current is ref, next is atom: return next atom. -/
  | curRefNextAtom {cr : CurId} {a : A} :
      ReconcileRootSpec curHeap nextHeap (.ref cr) (.atom a) (.atom a)
  /-- Both refs, kind mismatch: return next directly. -/
  | kindMismatch {cr : CurId} {nr : NextId}
      {cnd : Node A CurId} {nnd : Node A NextId} :
      curHeap.lookup cr = some cnd →
      nextHeap.lookup nr = some nnd →
      cnd.kind ≠ nnd.kind →
      ReconcileRootSpec curHeap nextHeap (.ref cr) (.ref nr)
        (nextRootImage (.ref nr))
  /-- Ref not resolved (node not in heap): return next. -/
  | refNotFound {cr : CurId} {nr : NextId} :
      (curHeap.lookup cr = none ∨ nextHeap.lookup nr = none) →
      ReconcileRootSpec curHeap nextHeap (.ref cr) (.ref nr)
        (nextRootImage (.ref nr))  -- next ref re-expressed in result namespace
  /-- Both refs, same kind: reconcile by kind-specific rule.
      Result reuses the current node. -/
  | sameKind {cr : CurId} {nr : NextId}
      {cnd : Node A CurId} {nnd : Node A NextId} :
      curHeap.lookup cr = some cnd →
      nextHeap.lookup nr = some nnd →
      cnd.kind = nnd.kind →
      ReconcileRootSpec curHeap nextHeap (.ref cr) (.ref nr)
        (.ref (.inl cr))

/-! ## Shared-object fast path (§5.4) -/

/-- When aligned entries are SameValue-equal and object-like. -/
inductive SharedObjectSpec
    (w : ReconcileWitness) :
    CurId → NextId → ResId → Prop where
  /-- Already imaged: return existing image. -/
  | alreadyImaged {cr : CurId} {nr : NextId} {ri : ResId} :
      w.image.lookup nr = some ri →
      SharedObjectSpec w cr nr ri
  /-- Current consumed by prior alignment: snapshot needed (fresh). -/
  | curConsumed {cr : CurId} {nr : NextId} {f : FreshId} :
      w.reuse.lookup cr ≠ none →
      w.image.lookup nr = none →
      SharedObjectSpec w cr nr (.inr f)
  /-- Shared: consume current for next, result reuses current. -/
  | shared {cr : CurId} {nr : NextId} :
      w.image.lookup nr = none →
      w.reuse.lookup cr = none →
      SharedObjectSpec w cr nr (.inl cr)

/-- Recursive value reconciliation rule (§5.3).
    This is what nested (non-root) reconciliation uses. -/
inductive ReconcileValueSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (w : ReconcileWitness) :
    Value A CurId → Value A NextId → Value A ResId → Prop where
  /-- Next is atom: return next. -/
  | nextAtom {cv : Value A CurId} {a : A} :
      ReconcileValueSpec curHeap nextHeap w cv (.atom a) (.atom a)
  /-- Next ref already imaged: return image. -/
  | alreadyImaged {cv : Value A CurId} {nr : NextId} {ri : ResId} :
      w.image.lookup nr = some ri →
      ReconcileValueSpec curHeap nextHeap w cv (.ref nr) (.ref ri)
  /-- Current is atom, next is ref: snapshot next subtree (fresh). -/
  | curAtomSnapshot {a : A} {nr : NextId} {f : FreshId} :
      ReconcileValueSpec curHeap nextHeap w (.atom a) (.ref nr) (.ref (.inr f))
  /-- Current already consumed: snapshot next subtree (fresh). -/
  | curConsumed {cr : CurId} {nr : NextId} {f : FreshId} :
      w.reuse.lookup cr ≠ none →
      w.image.lookup nr = none →
      ReconcileValueSpec curHeap nextHeap w (.ref cr) (.ref nr) (.ref (.inr f))
  /-- Kind mismatch: snapshot next subtree (fresh). -/
  | kindMismatch {cr : CurId} {nr : NextId} {f : FreshId}
      {cnd : Node A CurId} {nnd : Node A NextId} :
      curHeap.lookup cr = some cnd →
      nextHeap.lookup nr = some nnd →
      cnd.kind ≠ nnd.kind →
      w.reuse.lookup cr = none →
      w.image.lookup nr = none →
      ReconcileValueSpec curHeap nextHeap w (.ref cr) (.ref nr) (.ref (.inr f))
  /-- Same kind: reconcile by kind-specific rule, retain current. -/
  | reconcileByKind {cr : CurId} {nr : NextId}
      {cnd : Node A CurId} {nnd : Node A NextId} :
      curHeap.lookup cr = some cnd →
      nextHeap.lookup nr = some nnd →
      cnd.kind = nnd.kind →
      w.reuse.lookup cr = none →
      w.image.lookup nr = none →
      ReconcileValueSpec curHeap nextHeap w (.ref cr) (.ref nr) (.ref (.inl cr))

/-! ## Entry reconciliation rule (§5.5) -/

/-- Per-entry reconciliation for aligned children. -/
inductive ReconcileEntrySpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (w : ReconcileWitness) :
    Value A CurId → Value A NextId → Value A ResId → Prop where
  /-- SameValue atoms: return current. -/
  | sameAtom {a : A} :
      ReconcileEntrySpec curHeap nextHeap w (.atom a) (.atom a) (.atom a)
  /-- SameValue refs (shared objects): delegate to SharedObjectSpec. -/
  | sameRef {cr : CurId} {nr : NextId} {ri : ResId} :
      SharedObjectSpec w cr nr ri →
      ReconcileEntrySpec curHeap nextHeap w (.ref cr) (.ref nr) (.ref ri)
  /-- Different values: recursive reconcile via value rule (§5.3). -/
  | different {cv : Value A CurId} {nv : Value A NextId} {rv : Value A ResId} :
      ReconcileValueSpec curHeap nextHeap w cv nv rv →
      ReconcileEntrySpec curHeap nextHeap w cv nv rv

/-! ## Kind-specific node reconciliation (§6.1–6.8) -/

/-- A result value is either reconciled from a current-next pair,
    or is a fresh snapshot of next (when no current counterpart exists). -/
inductive ReconciledChild {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (w : ReconcileWitness) :
    Value A NextId → Value A ResId → Prop where
  /-- Reconciled from a specific current entry. -/
  | fromEntry {cv : Value A CurId} {nv : Value A NextId} {rv : Value A ResId} :
      ReconcileEntrySpec curHeap nextHeap w cv nv rv →
      ReconciledChild curHeap nextHeap w nv rv
  /-- Fresh snapshot of a next ref that does not already have an image. -/
  | freshRef {nr : NextId} {f : FreshId} :
      w.image.lookup nr = none →
      ReconciledChild curHeap nextHeap w (.ref nr) (.ref (.inr f))
  /-- Next atom passed through. -/
  | atom {a : A} :
      ReconciledChild curHeap nextHeap w (.atom a) (.atom a)

inductive ReconcileNodeSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (w : ReconcileWitness) :
    Node A CurId → Node A NextId → Node A ResId → Prop where
  /-- §6.8 Plain objects: result has next keys in next order,
      each value reconciled against current value at same key.
      Because reconcile retains and mutates the current object in place,
      the retained plain-object prototype stays at the current label `p₁`. -/
  | plainObject {p₁ : ProtoLabel} {f₁ : ObjFields A CurId}
      {p₂ : ProtoLabel} {f₂ : ObjFields A NextId}
      {fr : ObjFields A ResId} :
      fr.keys = f₂.keys →
      (∀ k vr, List.dlookup k fr = some vr →
        ∃ vn, List.dlookup k f₂ = some vn ∧
          ReconciledChild curHeap nextHeap w vn vr) →
      ReconcileNodeSpec curHeap nextHeap w
        (.plainObject p₁ f₁) (.plainObject p₂ f₂) (.plainObject p₁ fr)
  /-- §6.1 Arrays: index-aligned, same length as next. -/
  | array {ce : List (Option (Value A CurId))}
      {ne : List (Option (Value A NextId))}
      {re : List (Option (Value A ResId))} :
      re.length = ne.length →
      (∀ i (hi_n : i < ne.length) (hi_r : i < re.length),
        match ne[i] with
        | none => re[i] = none
        | some nv => ∃ rv, re[i] = some rv ∧
            ReconciledChild curHeap nextHeap w nv rv) →
      ReconcileNodeSpec curHeap nextHeap w (.array ce) (.array ne) (.array re)
  /-- §6.2 Date: next timestamp wins. -/
  | date {ms₁ ms₂ : Int} :
      ReconcileNodeSpec curHeap nextHeap w (.date ms₁) (.date ms₂) (.date ms₂)
  /-- §6.3 Map: ordinal-aligned entry sequences. -/
  | map {ce : List (Value A CurId × Value A CurId)}
      {ne : List (Value A NextId × Value A NextId)}
      {re : List (Value A ResId × Value A ResId)} :
      re.length = ne.length →
      (∀ i (hi_n : i < ne.length) (hi_r : i < re.length),
        ReconciledChild curHeap nextHeap w (ne[i]).1 (re[i]).1 ∧
        ReconciledChild curHeap nextHeap w (ne[i]).2 (re[i]).2) →
      ReconcileNodeSpec curHeap nextHeap w (.map ce) (.map ne) (.map re)
  /-- §6.4 Set: ordinal-aligned value sequences. -/
  | set {cv : List (Value A CurId)}
      {nv : List (Value A NextId)}
      {rv : List (Value A ResId)} :
      rv.length = nv.length →
      (∀ i (hi_n : i < nv.length) (hi_r : i < rv.length),
        ReconciledChild curHeap nextHeap w nv[i] rv[i]) →
      ReconcileNodeSpec curHeap nextHeap w (.set cv) (.set nv) (.set rv)
  /-- §6.5 ArrayBuffer: bytes from next. -/
  | arrayBuffer {cb nb : List UInt8} :
      ReconcileNodeSpec curHeap nextHeap w
        (.arrayBuffer cb) (.arrayBuffer nb) (.arrayBuffer nb)
  /-- §6.6 DataView: reconcile buffer, next metadata. -/
  | dataView {cb : CurId} {nb : NextId} {rb : ResId}
      {cOff cLen nOff nLen : Nat} :
      ReconciledChild curHeap nextHeap w (.ref nb) (.ref rb) →
      ReconcileNodeSpec curHeap nextHeap w
        (.dataView cb cOff cLen) (.dataView nb nOff nLen)
        (.dataView rb nOff nLen)
  /-- §6.7 TypedArray: reconcile buffer + elements, next metadata. -/
  | typedArray {cTag : CtorTag} {cb : CurId} {nb : NextId} {rb : ResId}
      {nTag : CtorTag} {cOff cLen nOff nLen : Nat}
      {cElems : List (Value A CurId)}
      {nElems : List (Value A NextId)}
      {rElems : List (Value A ResId)} :
      ReconciledChild curHeap nextHeap w (.ref nb) (.ref rb) →
      rElems.length = nElems.length →
      (∀ i (hi_n : i < nElems.length) (hi_r : i < rElems.length),
        ReconciledChild curHeap nextHeap w nElems[i] rElems[i]) →
      ReconcileNodeSpec curHeap nextHeap w
        (.typedArray cTag cb cOff cLen cElems)
        (.typedArray nTag nb nOff nLen nElems)
        (.typedArray nTag rb nOff nLen rElems)

/-! ## Full reconcile specification -/

/-- A reconcile result satisfies this specification when:
    - the root rule determines the result,
    - a witness exists satisfying all invariants,
    - for same-kind roots, the result node satisfies the kind-specific spec,
    - the result is surface-equivalent to next. -/
structure ReconcileSpec {A : Type} [AtomEq A]
    (curHeap : Heap A CurId) (nextHeap : Heap A NextId)
    (resultHeap : Heap A ResId)
    (curRoot : Value A CurId) (nextRoot : Value A NextId)
    (resultRoot : Value A ResId) : Prop where
  /-- The root rule holds. -/
  rootSpec : ReconcileRootSpec curHeap nextHeap curRoot nextRoot resultRoot
  /-- There exists a witness satisfying invariants. -/
  witness : ∃ w : ReconcileWitness, WitnessInv w
  /-- For same-kind root refs, the retained result root is the witness image of
      the corresponding next root. -/
  rootImageSpec : ∀ (w : ReconcileWitness) (cr : CurId) (nr : NextId)
      (cnd : Node A CurId) (nnd : Node A NextId),
      curHeap.lookup cr = some cnd →
      nextHeap.lookup nr = some nnd →
      cnd.kind = nnd.kind →
      resultRoot = .ref (.inl cr) →
      w.image.lookup nr = some (.inl cr)
  /-- For same-kind root refs, the result node is in the result heap
      and satisfies the kind-specific reconciliation spec. -/
  nodeSpec : ∀ (w : ReconcileWitness) (cr : CurId) (nr : NextId)
      (cnd : Node A CurId) (nnd : Node A NextId),
      curHeap.lookup cr = some cnd →
      nextHeap.lookup nr = some nnd →
      cnd.kind = nnd.kind →
      resultRoot = .ref (.inl cr) →
      ∃ rnd : Node A ResId,
        resultHeap.lookup (.inl cr) = some rnd ∧
        ReconcileNodeSpec curHeap nextHeap w cnd nnd rnd
  /-- Cycle preservation: if a next node is on a non-empty cycle and the
      witness maps it to a result node, then the result node is on a
      corresponding non-empty cycle. -/
  cyclePres : ∀ (w : ReconcileWitness) (nr : NextId) (ri : ResId),
      w.image.lookup nr = some ri →
      Relation.TransGen (edge nextHeap) nr nr →
      Relation.TransGen (edge resultHeap) ri ri
  /-- The result is surface-equivalent to next.
      This is the obligation discharged by Iteration 8 (refinement proof)
      when the executable algorithm constructs a `ReconcileSpec`. -/
  surfaceEq : SurfaceEq nextHeap resultHeap nextRoot resultRoot

/-! ## Theorem statements (Iteration 6 — proofs later) -/

/-- R4 — Root fast-path: SameValue atoms ⇒ return current. -/
theorem reconcile_root_fastpath {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {nextHeap : Heap A NextId}
    {a : A} :
    ReconcileRootSpec curHeap nextHeap (.atom a) (.atom a) (.atom a) :=
  .sameAtom

/-- R5 — Root replacement: current ref, next atom ⇒ return the canonical
    result-namespace image of next (which is just the atom itself). -/
theorem reconcile_root_next_atom {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {nextHeap : Heap A NextId}
    {cr : CurId} {a : A} :
    ReconcileRootSpec curHeap nextHeap (.ref cr) (.atom a) (nextRootImage (.atom a)) :=
  .curRefNextAtom

/-- R5 — Root replacement: current atom, next ref ⇒ the result is the
    canonical result-namespace image of next. -/
theorem reconcile_root_curAtomNextRef {A : Type} [AtomEq A]
    {curHeap : Heap A CurId} {nextHeap : Heap A NextId}
    {a : A} {nr : NextId} :
    ReconcileRootSpec curHeap nextHeap (.atom a) (.ref nr) (nextRootImage (.ref nr)) :=
  .curAtomNextRef

/-- R7 — Sharing: equal next refs → equal result images (from witness). -/
theorem reconcile_sharing
    {w : ReconcileWitness} (hinv : WitnessInv w)
    {n : NextId} {r₁ r₂ : ResId}
    (h₁ : w.image.lookup n = some r₁)
    (h₂ : w.image.lookup n = some r₂) :
    r₁ = r₂ :=
  hinv.imageFun n r₁ r₂ h₁ h₂

/-- R8 — No-collapse: distinct next refs → distinct result images. -/
theorem reconcile_no_collapse
    {w : ReconcileWitness} (hinv : WitnessInv w)
    {n₁ n₂ : NextId} {r₁ r₂ : ResId}
    (hne : n₁ ≠ n₂)
    (h₁ : w.image.lookup n₁ = some r₁)
    (h₂ : w.image.lookup n₂ = some r₂) :
    r₁ ≠ r₂ :=
  hinv.noCollapse n₁ n₂ hne r₁ r₂ h₁ h₂

/-- R9 — Current-node injectivity (from reuse injectivity). -/
theorem reconcile_current_injectivity
    {w : ReconcileWitness} (hinv : WitnessInv w)
    {c₁ c₂ : CurId} {n : NextId}
    (h₁ : w.reuse.lookup c₁ = some n)
    (h₂ : w.reuse.lookup c₂ = some n) :
    c₁ = c₂ :=
  hinv.reuseInj c₁ c₂ n h₁ h₂

end Reconcile
