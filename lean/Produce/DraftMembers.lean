/-!
# Draft members

Inside a recipe the same object can appear as itself, as its draft, or as a Vue reactive proxy of
it. Where the library decides membership, it compares member identities: a draft counts as the
object it drafts and a Vue proxy as its raw object, which is the same object (`StorageViews`), as
Vue's own methods count it; outside Vue reactive state a search for a raw object can miss a Vue
proxy of it (`plainTargets`). `Set` drafts do so in `has` and in
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

/-! ## Looking a value up by several identities

Outside Vue reactive state a value's key is the storage of its draft when it has one, which every
view of that storage shares whichever view the draft was made from, and otherwise the value
itself, or the original of a copy. A searched value is looked up by its key and by its key's raw
object (`plainTargets`). The searched value's key is taken before the search reads any element,
and reading an element can draft it, changing its key from the value to its storage
(`plain_self_staged`). A search therefore finds an element the array holds (`plain_self`,
`plain_self_staged`), the raw object of a searched Vue proxy (`plain_raw`) and every object that
shares the searched value's key (`plain_shared`), and only objects of the searched value's storage
(`plain_sound`). A search for a raw object finds a Vue proxy of it only through a draft of one of
them. In Vue reactive state both sides are raw objects: that is the search above with
`storage ∘ key` as the identity (`includesBy_single`).
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

section Plain

variable {γ : Type} [DecidableEq γ] (key storage : γ → γ)

/-- What a search outside Vue reactive state looks a value up by: its key and its key's raw
object. -/
def plainTargets (x : γ) : List γ := [key x, storage (key x)]

/-- A search finds an element the array holds. -/
theorem plain_self (elements : List γ) (x : γ) (hx : x ∈ elements) :
    includesBy key (plainTargets key storage) elements x = true :=
  (includesBy_iff _ _ _ _).mpr ⟨x, hx, by simp [plainTargets]⟩

/-- A search for a Vue proxy finds its raw object. -/
theorem plain_raw (elements : List γ) (x e : γ) (he : e ∈ elements)
    (h : key e = storage (key x)) :
    includesBy key (plainTargets key storage) elements x = true :=
  (includesBy_iff _ _ _ _).mpr ⟨e, he, by simp [plainTargets, h]⟩

/-- A search finds every object that shares the searched value's key. -/
theorem plain_shared (elements : List γ) (x e : γ) (he : e ∈ elements) (h : key e = key x) :
    includesBy key (plainTargets key storage) elements x = true :=
  (includesBy_iff _ _ _ _).mpr ⟨e, he, by simp [plainTargets, h]⟩

/-- A search finds only objects of the searched value's storage. -/
theorem plain_sound (idem : ∀ v, storage (storage v) = storage v) (elements : List γ) (x : γ)
    (h : includesBy key (plainTargets key storage) elements x = true) :
    ∃ e ∈ elements, storage (key e) = storage (key x) := by
  obtain ⟨e, he, ht⟩ := (includesBy_iff _ _ _ _).mp h
  refine ⟨e, he, ?_⟩
  simp only [plainTargets, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht
  · rw [ht]
  · rw [ht, idem]

end Plain

/-- The key of a drafted value is the storage of its draft's base, the same for every view of
one storage whichever view the draft was made from. -/
theorem drafted_key {γ : Type} (storage base : γ → γ)
    (hb : ∀ v, storage (base v) = storage v) (v w : γ) (h : storage v = storage w) : storage (base v) = storage (base w) := by
  rw [hb, hb, h]

/-- The searched value's key is taken before the search reads an element, `after` gives each
element's key once read, and reading changes a key at most from the value to its storage. A
search still finds an element the array holds. -/
theorem plain_self_staged {γ : Type} [DecidableEq γ] (storage before after : γ → γ)
    (elements : List γ) (x : γ) (hx : x ∈ elements)
    (hafter : after x = before x ∨ after x = storage (before x)) :
    includesBy after (plainTargets before storage) elements x = true :=
  (includesBy_iff _ _ _ _).mpr ⟨x, hx, by
    rcases hafter with h | h <;> simp [plainTargets, h]⟩

end Reconcile.DraftMembers
