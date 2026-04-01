/-
  Reconcile — reachability, edge relation, and observational surface equivalence.

  Defines:
    - edge relation from heap payloads
    - Reachable via Relation.ReflTransGen
    - SurfaceEq: the main correctness relation
    - SameShape: kind-compatibility predicate
-/

import Defs
import Mathlib.Logic.Relation

namespace Reconcile

open Relation

/-! ## Edge relation -/

/-- One-step directed edge in a heap: `edge h a b` iff node `a` has a child
    reference to `b`. -/
def edge {A : Type} {ι : Type} [DecidableEq ι] (h : Heap A ι) (a b : ι) : Prop :=
  ∃ node, h.lookup a = some node ∧ b ∈ node.childRefs

/-- Reachability in a heap via reflexive-transitive closure of `edge`. -/
def Reachable {A : Type} {ι : Type} [DecidableEq ι] (h : Heap A ι) : ι → ι → Prop :=
  ReflTransGen (edge h)

/-- A node is reachable from a root value. -/
def ReachableFromRoot {A : Type} {ι : Type} [DecidableEq ι]
    (h : Heap A ι) (root : Value A ι) (target : ι) : Prop :=
  match root with
  | .atom _ => False
  | .ref r  => Reachable h r target

/-! ## Same shape (kind compatibility) -/

/-- Two nodes have the same shape iff they have the same kind tag. -/
def SameShape {A : Type} {ι₁ ι₂ : Type} (n₁ : Node A ι₁) (n₂ : Node A ι₂) : Prop :=
  n₁.kind = n₂.kind

@[simp] theorem SameShape_iff {A : Type} {ι₁ ι₂ : Type}
    (n₁ : Node A ι₁) (n₂ : Node A ι₂) :
    SameShape n₁ n₂ ↔ n₁.kind = n₂.kind := Iff.rfl

/-! ## Surface equivalence -/

/-- Abstract atomic equality. Parameterized to stay JS-free.
    In the intended instantiation this is SameValue. -/
class AtomEq (A : Type) where
  eq : A → A → Prop
  eq_dec : DecidableRel eq
  eq_refl : ∀ a, eq a a

attribute [instance] AtomEq.eq_dec

/-- Option-level value equivalence: both none, or both some with a given
    relation on values. -/
def OptionRel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

/-- Depth-bounded surface equivalence between values in two heaps.
    Uses an explicit Nat depth parameter to stay in Lean's inductive
    fragment while handling cyclic heaps.

    Atom comparisons don't consume depth. Ref-following consumes one level.
    Within a node, all children are compared at the remaining depth.

    We define this as a recursive Prop-valued function rather than an
    inductive to avoid mutual/nested inductive difficulties. -/
def SurfaceEqBounded {A : Type} [AtomEq A] {ι₁ ι₂ : Type}
    [DecidableEq ι₁] [DecidableEq ι₂]
    (h₁ : Heap A ι₁) (h₂ : Heap A ι₂) :
    Nat → Value A ι₁ → Value A ι₂ → Prop
  | _, .atom a₁, .atom a₂ => AtomEq.eq a₁ a₂
  | 0, .ref _, .ref _ => True  -- at depth 0 any two refs are trivially ok
  | n + 1, .ref r₁, .ref r₂ =>
    match h₁.lookup r₁, h₂.lookup r₂ with
    | some nd₁, some nd₂ => NodeSurfaceEqBounded h₁ h₂ n nd₁ nd₂
    | _, _ => False
  | _, .atom _, .ref _ => False
  | _, .ref _, .atom _ => False
where
  /-- Node-level surface equivalence at a given depth. -/
  NodeSurfaceEqBounded {A : Type} [AtomEq A] {ι₁ ι₂ : Type}
      [DecidableEq ι₁] [DecidableEq ι₂]
      (h₁ : Heap A ι₁) (h₂ : Heap A ι₂)
      (n : Nat) : Node A ι₁ → Node A ι₂ → Prop
    | .plainObject _ f₁, .plainObject _ f₂ =>
      f₁.keys = f₂.keys ∧
      ∀ k v₁ v₂, List.dlookup k f₁ = some v₁ → List.dlookup k f₂ = some v₂ →
        SurfaceEqBounded h₁ h₂ n v₁ v₂
    | .array es₁, .array es₂ =>
      es₁.length = es₂.length ∧
      ∀ i (hi₁ : i < es₁.length) (hi₂ : i < es₂.length),
        OptionRel (SurfaceEqBounded h₁ h₂ n) es₁[i] es₂[i]
    | .date ms₁, .date ms₂ => ms₁ = ms₂
    | .map es₁, .map es₂ =>
      es₁.length = es₂.length ∧
      ∀ i (hi₁ : i < es₁.length) (hi₂ : i < es₂.length),
        SurfaceEqBounded h₁ h₂ n (es₁[i]).1 (es₂[i]).1 ∧
        SurfaceEqBounded h₁ h₂ n (es₁[i]).2 (es₂[i]).2
    | .set vs₁, .set vs₂ =>
      vs₁.length = vs₂.length ∧
      ∀ i (hi₁ : i < vs₁.length) (hi₂ : i < vs₂.length),
        SurfaceEqBounded h₁ h₂ n vs₁[i] vs₂[i]
    | .arrayBuffer bs₁, .arrayBuffer bs₂ => bs₁ = bs₂
    | .dataView b₁ off₁ len₁, .dataView b₂ off₂ len₂ =>
      off₁ = off₂ ∧ len₁ = len₂ ∧
      SurfaceEqBounded h₁ h₂ n (.ref b₁) (.ref b₂)
    | .typedArray tag₁ b₁ off₁ len₁ elems₁,
      .typedArray tag₂ b₂ off₂ len₂ elems₂ =>
      tag₁ = tag₂ ∧ off₁ = off₂ ∧ len₁ = len₂ ∧
      SurfaceEqBounded h₁ h₂ n (.ref b₁) (.ref b₂) ∧
      elems₁.length = elems₂.length ∧
      ∀ i (hi₁ : i < elems₁.length) (hi₂ : i < elems₂.length),
        SurfaceEqBounded h₁ h₂ n elems₁[i] elems₂[i]
    | _, _ => False

/-- Full surface equivalence: equivalent at every finite depth.
    For finite heaps, equivalence at depth ≥ heap size suffices. -/
def SurfaceEq {A : Type} [AtomEq A] {ι₁ ι₂ : Type}
    [DecidableEq ι₁] [DecidableEq ι₂]
    (h₁ : Heap A ι₁) (h₂ : Heap A ι₂)
    (v₁ : Value A ι₁) (v₂ : Value A ι₂) : Prop :=
  ∀ n, SurfaceEqBounded h₁ h₂ n v₁ v₂

/-! ## Basic SurfaceEqBounded lemmas -/

@[simp] theorem SurfaceEqBounded_atom {A : Type} [AtomEq A] {ι₁ ι₂ : Type}
    [DecidableEq ι₁] [DecidableEq ι₂]
    {h₁ : Heap A ι₁} {h₂ : Heap A ι₂} {n : Nat} {a₁ a₂ : A} :
    SurfaceEqBounded h₁ h₂ n (.atom a₁) (.atom a₂) ↔ AtomEq.eq a₁ a₂ := by
  cases n <;> simp [SurfaceEqBounded]

@[simp] theorem SurfaceEqBounded_atom_ref {A : Type} [AtomEq A] {ι₁ ι₂ : Type}
    [DecidableEq ι₁] [DecidableEq ι₂]
    {h₁ : Heap A ι₁} {h₂ : Heap A ι₂} {n : Nat} {a : A} {r : ι₂} :
    SurfaceEqBounded h₁ h₂ n (.atom a) (.ref r) ↔ False := by
  cases n <;> simp [SurfaceEqBounded]

@[simp] theorem SurfaceEqBounded_ref_atom {A : Type} [AtomEq A] {ι₁ ι₂ : Type}
    [DecidableEq ι₁] [DecidableEq ι₂]
    {h₁ : Heap A ι₁} {h₂ : Heap A ι₂} {n : Nat} {r : ι₁} {a : A} :
    SurfaceEqBounded h₁ h₂ n (.ref r) (.atom a) ↔ False := by
  cases n <;> simp [SurfaceEqBounded]

/-! ## Topology preservation definitions -/

/-- Sharing preservation: equal next refs map to equal result refs. -/
def SharingPreserved (image : NextId → Option ResId) : Prop :=
  ∀ n, image n ≠ none → ∀ n', n = n' → image n = image n'

/-- No-collapse: distinct next refs map to distinct result refs. -/
def NoCollapse (image : NextId → Option ResId) : Prop :=
  ∀ n₁ n₂, n₁ ≠ n₂ → image n₁ ≠ none → image n₂ ≠ none →
    image n₁ ≠ image n₂

/-- Current-node injectivity: at most one next node per current node. -/
def CurrentInjectivity (reuse : CurId → Option NextId) : Prop :=
  ∀ c n₁ n₂, reuse c = some n₁ → reuse c = some n₂ → n₁ = n₂

/-- Image–reuse consistency: if a current node is an image, it is reused. -/
def ImageReuseConsistent
    (reuse : CurId → Option NextId) (image : NextId → Option ResId) : Prop :=
  ∀ n c, image n = some (.inl c) → reuse c = some n

/-- Bundled topology-preservation predicate for an image/reuse witness pair.
    Combines sharing, no-collapse, injectivity, and consistency. -/
structure ImagesPreserveTopology
    (reuse : CurId → Option NextId)
    (image : NextId → Option ResId) : Prop where
  sharing : SharingPreserved image
  noCollapse : NoCollapse image
  curInj : CurrentInjectivity reuse
  consistency : ImageReuseConsistent reuse image

end Reconcile
