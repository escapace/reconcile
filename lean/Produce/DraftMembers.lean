/-!
# Draft members

Inside a recipe the same object can appear as itself or as its draft. Where the library decides
membership, it compares member identities: a draft counts as the object it drafts. `Set` drafts
do so in `has` and in
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

/-! ## Looking a value up by a key taken before the search

A value's key is the object its draft drafts when it has one, and otherwise the value itself, or
the original of a copy. The searched value's key is taken before the search reads any element
(`target`), and each element's key is taken once it is read (`held`); reading an element does not
change its key, so a search finds an element the array holds (`plain_self`).
-/

/-- `includes`, comparing each element's key with the searched value's. -/
def includesBy (held target : α → β) (elements : List α) (x : α) : Bool :=
  elements.any fun e => held e == target x

def indexOfBy (held target : α → β) (elements : List α) (x : α) : Option Nat :=
  elements.findIdx? fun e => held e == target x

def lastIndexOfBy (held target : α → β) (elements : List α) (x : α) : Option Nat :=
  (elements.reverse.findIdx? fun e => held e == target x).map (elements.length - 1 - ·)

/-- With one key for every value, a search is `includes`. -/
theorem includesBy_single (identity : α → β) (elements : List α) (x : α) :
    includesBy identity identity elements x = includes identity elements x := rfl

theorem includesBy_iff (held target : α → β) (elements : List α) (x : α) :
    includesBy held target elements x = true ↔ ∃ e ∈ elements, held e = target x := by
  simp [includesBy]

/-- A search finds the same elements whether the array holds objects or their drafts. -/
theorem includesBy_drafted (held target : α → β) (draft : α → α)
    (same : ∀ a, held (draft a) = held a) (elements : List α) (x : α) :
    includesBy held target (elements.map draft) x = includesBy held target elements x := by
  simp only [includesBy, List.any_map, Function.comp_def, same]

theorem indexOfBy_drafted (held target : α → β) (draft : α → α)
    (same : ∀ a, held (draft a) = held a) (elements : List α) (x : α) :
    indexOfBy held target (elements.map draft) x = indexOfBy held target elements x := by
  simp only [indexOfBy, List.findIdx?_map, Function.comp_def, same]

theorem lastIndexOfBy_drafted (held target : α → β) (draft : α → α)
    (same : ∀ a, held (draft a) = held a) (elements : List α) (x : α) :
    lastIndexOfBy held target (elements.map draft) x = lastIndexOfBy held target elements x := by
  simp only [lastIndexOfBy, ← List.map_reverse, List.findIdx?_map, Function.comp_def, same,
    List.length_map]

/-- Searching for values with the same key gives the same answer. -/
theorem includesBy_form (held target : α → β) (elements : List α) (x y : α)
    (h : target x = target y) :
    includesBy held target elements x = includesBy held target elements y := by
  simp [includesBy, h]

/-- A search finds an element the array holds, whose key once read is the key taken for it
before the search. -/
theorem plain_self {γ : Type} [DecidableEq γ] (before after : γ → γ) (elements : List γ) (x : γ)
    (hx : x ∈ elements) (hafter : after x = before x) :
    includesBy after before elements x = true :=
  (includesBy_iff _ _ _ _).mpr ⟨x, hx, hafter⟩

end Reconcile.DraftMembers
