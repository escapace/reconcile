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

/-! ## Looking a value up by a key taken before the search

A value's key is the object its draft drafts when it has one, and otherwise the value itself, or
the original of a copy. The searched value's key is taken before the search reads any element
(`targets`), and each element's key is taken once it is read (`held`); reading an element does not
change its key, so a search finds an element the array holds (`plain_self`).
-/

/-- `includes`, comparing each element's identity with those the searched value is looked up
by. -/
def includesBy (held : α → β) (targets : α → List β) (elements : List α) (x : α) : Bool :=
  elements.any fun e => held e ∈ targets x

def indexOfBy (held : α → β) (targets : α → List β) (elements : List α) (x : α) : Option Nat :=
  elements.findIdx? fun e => held e ∈ targets x

def lastIndexOfBy (held : α → β) (targets : α → List β) (elements : List α) (x : α) :
    Option Nat :=
  (elements.reverse.findIdx? fun e => held e ∈ targets x).map (elements.length - 1 - ·)

/-- Looked up by its own identity alone, a value is searched for as by `includes`. -/
theorem includesBy_single (identity : α → β) (elements : List α) (x : α) :
    includesBy identity (fun y => [identity y]) elements x = includes identity elements x := by
  simp only [includesBy, includes, List.mem_singleton]; rfl

theorem indexOfBy_single (identity : α → β) (elements : List α) (x : α) :
    indexOfBy identity (fun y => [identity y]) elements x = indexOf identity elements x := by
  simp only [indexOfBy, indexOf, List.mem_singleton]; rfl

theorem lastIndexOfBy_single (identity : α → β) (elements : List α) (x : α) :
    lastIndexOfBy identity (fun y => [identity y]) elements x =
      lastIndexOf identity elements x := by
  simp only [lastIndexOfBy, lastIndexOf, List.mem_singleton]; rfl

theorem includesBy_iff (held : α → β) (targets : α → List β) (elements : List α) (x : α) :
    includesBy held targets elements x = true ↔ ∃ e ∈ elements, held e ∈ targets x := by
  simp [includesBy]

/-- A search finds the same elements whether the array holds objects or their drafts. -/
theorem includesBy_drafted (held : α → β) (targets : α → List β) (draft : α → α)
    (same : ∀ a, held (draft a) = held a) (elements : List α) (x : α) :
    includesBy held targets (elements.map draft) x = includesBy held targets elements x := by
  simp only [includesBy, List.any_map, Function.comp_def, same]

theorem indexOfBy_drafted (held : α → β) (targets : α → List β) (draft : α → α)
    (same : ∀ a, held (draft a) = held a) (elements : List α) (x : α) :
    indexOfBy held targets (elements.map draft) x = indexOfBy held targets elements x := by
  simp only [indexOfBy, List.findIdx?_map, Function.comp_def, same]

theorem lastIndexOfBy_drafted (held : α → β) (targets : α → List β) (draft : α → α)
    (same : ∀ a, held (draft a) = held a) (elements : List α) (x : α) :
    lastIndexOfBy held targets (elements.map draft) x =
      lastIndexOfBy held targets elements x := by
  simp only [lastIndexOfBy, ← List.map_reverse, List.findIdx?_map, Function.comp_def, same,
    List.length_map]

/-- Searching for values looked up by the same identities gives the same answer. -/
theorem includesBy_form (held : α → β) (targets : α → List β) (elements : List α) (x y : α)
    (h : targets x = targets y) :
    includesBy held targets elements x = includesBy held targets elements y := by
  simp [includesBy, h]

theorem indexOfBy_form (held : α → β) (targets : α → List β) (elements : List α) (x y : α)
    (h : targets x = targets y) :
    indexOfBy held targets elements x = indexOfBy held targets elements y := by
  simp [indexOfBy, h]

/-- A search finds an element the array holds, whose key once read is the key taken for it
before the search. -/
theorem plain_self {γ : Type} [DecidableEq γ] (before after : γ → γ) (elements : List γ) (x : γ)
    (hx : x ∈ elements) (hafter : after x = before x) :
    includesBy after (fun y => [before y]) elements x = true :=
  (includesBy_iff _ _ _ _).mpr ⟨x, hx, by simp [hafter]⟩

end Reconcile.DraftMembers
