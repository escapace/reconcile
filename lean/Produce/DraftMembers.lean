/-!
# Draft members

Inside a recipe the same object can appear as itself, as its draft, or as a Vue reactive proxy of
it. Where the library decides membership, it compares member identities: a draft counts as the
object it drafts and, in Vue reactive state, a Vue proxy as its raw object, as Vue's own methods
count it; in plain state a Vue proxy is an object of its own. `Set` drafts do so in `has` and in
`Set` methods (`DraftSetMethods`), `Map` drafts in key lookup, and array drafts in `includes`,
`indexOf` and `lastIndexOf`, which replace the native methods: they follow the native search, from
`fromIndex` and stopping at the first match, but compare the identities of the elements. A
subclass override still runs. JavaScript `===` compares references and cannot do this. The model
covers the whole array; `fromIndex` and the reads a search makes are checked natively.

`identity` maps a value to its member identity; `draft` maps an element to what a read of the
array draft returns.
-/

namespace Reconcile.DraftMembers

variable {α β : Type} [DecidableEq β]

/-- `includes`: some element has the searched value's identity. -/
def includes (identity : α → β) (elements : List α) (x : α) : Bool :=
  elements.any fun e => identity e == identity x

/-- `indexOf`: the first element with the searched value's identity. -/
def indexOf (identity : α → β) (elements : List α) (x : α) : Option Nat :=
  elements.findIdx? fun e => identity e == identity x

/-- `lastIndexOf`: the last element with the searched value's identity. -/
def lastIndexOf (identity : α → β) (elements : List α) (x : α) : Option Nat :=
  (elements.reverse.findIdx? fun e => identity e == identity x).map (elements.length - 1 - ·)

/-- A search finds the same elements whether the array holds objects or their drafts. -/
theorem includes_drafted (identity : α → β) (draft : α → α)
    (same : ∀ a, identity (draft a) = identity a) (elements : List α) (x : α) :
    includes identity (elements.map draft) x = includes identity elements x := by
  simp only [includes, List.any_map, Function.comp_def, same]

theorem indexOf_drafted (identity : α → β) (draft : α → α)
    (same : ∀ a, identity (draft a) = identity a) (elements : List α) (x : α) :
    indexOf identity (elements.map draft) x = indexOf identity elements x := by
  simp only [indexOf, List.findIdx?_map, Function.comp_def, same]

theorem lastIndexOf_drafted (identity : α → β) (draft : α → α)
    (same : ∀ a, identity (draft a) = identity a) (elements : List α) (x : α) :
    lastIndexOf identity (elements.map draft) x = lastIndexOf identity elements x := by
  simp only [lastIndexOf, ← List.map_reverse, List.findIdx?_map, Function.comp_def, same,
    List.length_map]

/-- Searching for a value or for any form of it, such as its draft, gives the same answer. -/
theorem includes_form (identity : α → β) (elements : List α) (x y : α)
    (h : identity x = identity y) : includes identity elements x = includes identity elements y := by
  simp [includes, h]

theorem indexOf_form (identity : α → β) (elements : List α) (x y : α)
    (h : identity x = identity y) : indexOf identity elements x = indexOf identity elements y := by
  simp [indexOf, h]

end Reconcile.DraftMembers
