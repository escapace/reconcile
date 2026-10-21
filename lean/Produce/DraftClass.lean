/-!
# Draft class

A `Map` or `Set` draft is a wrapper that records changes instead of applying them. Its prototype
chain is one draft layer, holding the collection methods that read and record, followed by the
source's own chain. So a draft is an instance of every class the source is an instance of,
`Symbol.toStringTag` and methods a subclass adds resolve as on the source, and a collection
method resolves to the draft's. The draft's method acts on the original until the first change and
on a working copy of the same class afterwards, through that object's own methods, so a subclass
override still runs on a native collection, where its `super` calls work.

Prototypes are identifiers, a chain lists them from the nearest one, and `own p n` is the method
prototype `p` defines for name `n`.
-/

namespace Reconcile.DraftClass

/-- The draft's chain: the draft layer, then the source's chain. -/
def draftChain (layer : Nat) (source : List Nat) : List Nat := layer :: source

/-- `instanceof C` holds when `C.prototype` is on the chain. -/
def instanceOf (chain : List Nat) (c : Nat) : Bool := chain.contains c

/-- The first definition of a name along a chain. -/
def lookup (own : Nat → String → Option Nat) : List Nat → String → Option Nat
  | [], _ => none
  | p :: ps, n => (own p n).orElse fun _ => lookup own ps n

/-- The layer defines exactly the collection methods; other prototypes keep their own. -/
def withLayer (layer : Nat) (methods : List String) (draft : String → Nat)
    (own : Nat → String → Option Nat) (p : Nat) (n : String) : Option Nat :=
  if p = layer then (if n ∈ methods then some (draft n) else none) else own p n

/-- A draft is an instance of exactly the classes its source is an instance of. -/
theorem draft_instanceOf (layer c : Nat) (source : List Nat) (h : c ≠ layer) :
    instanceOf (draftChain layer source) c = instanceOf source c := by
  simp only [instanceOf, draftChain, List.contains_cons, Bool.or_eq_right_iff_imp, beq_iff_eq]
  intro e
  exact absurd e h

/-- A name other than a collection method, such as a subclass method or `Symbol.toStringTag`,
resolves on the draft as on the source. -/
theorem lookup_other (layer : Nat) (methods : List String) (draft : String → Nat)
    (own : Nat → String → Option Nat) (source : List Nat) (n : String)
    (hn : n ∉ methods) (hl : layer ∉ source) :
    lookup (withLayer layer methods draft own) (draftChain layer source) n =
      lookup own source n := by
  have rest : ∀ s : List Nat, layer ∉ s →
      lookup (withLayer layer methods draft own) s n = lookup own s n := by
    intro s
    induction s with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      have hp : p ≠ layer := fun e => h (e ▸ List.mem_cons_self ..)
      have hps : layer ∉ ps := fun m => h (List.mem_cons_of_mem _ m)
      simp [lookup, withLayer, hp, ih hps]
  simp [draftChain, lookup, withLayer, hn, rest source hl]

/-- A collection method resolves to the draft's, whatever the source's chain defines. -/
theorem lookup_method (layer : Nat) (methods : List String) (draft : String → Nat)
    (own : Nat → String → Option Nat) (source : List Nat) (n : String) (hn : n ∈ methods) :
    lookup (withLayer layer methods draft own) (draftChain layer source) n = some (draft n) := by
  simp [draftChain, lookup, withLayer, hn]

end Reconcile.DraftClass
