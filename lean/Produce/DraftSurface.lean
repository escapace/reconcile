/-!
# Draft write surface

The heap model (`Defs`) represents a plain object or class instance by its own properties, an
array by its length and index entries, and a `Map`, `Set`, `Date`, buffer, view, URL or
Temporal value by its native content, with no other own properties. Every function of the
library carries only that surface, so a recipe write outside it could only be lost.

A draft therefore admits exactly the writes the model represents and refuses the others the way
a non-extensible object does: the assignment or deletion fails, which throws a `TypeError` in
strict-mode code, instead of being accepted and then dropped.
-/

namespace Reconcile.DraftSurface

/-- Draft representations: property drafts of objects and arrays, collection drafts, and the
writable copies of native values. -/
inductive Kind where
  | object
  | array
  | collection
  | typed
  | native
  deriving DecidableEq, Repr

/-- Keys a recipe can write: an array index, `length`, or any other property name or symbol. -/
inductive Key where
  | index
  | length
  | other
  deriving DecidableEq, Repr

/-- Whether the heap model represents an own property with this key on this kind. -/
def represented : Kind → Key → Bool
  | .object, _ => true
  | .array, .index => true
  | .array, .length => true
  | .array, .other => false
  | .collection, _ => false
  | .typed, .index => true
  | .typed, _ => false
  | .native, _ => false

/-- The runtime's admission: object drafts accept every property; array drafts accept indices and
`length`; collection drafts and native copies are non-extensible, so they accept no new own
property, and a typed-array copy's indices are its elements. -/
def admits (kind : Kind) (key : Key) : Bool :=
  match kind with
  | .object => true
  | .array => key != .other
  | .collection => false
  | .typed => key == .index
  | .native => false

/-- A draft accepts a write exactly when the result can carry it, so no accepted write is lost. -/
theorem admits_iff_represented (kind : Kind) (key : Key) :
    admits kind key = represented kind key := by
  cases kind <;> cases key <;> rfl

/-- The refused writes are the ones a draft that accepted them would drop from its result. -/
theorem refused (kind : Kind) (key : Key) :
    admits kind key = false ↔ kind ≠ .object ∧ (kind = .collection ∨ kind = .native ∨
      key = .other ∨ (kind = .typed ∧ key = .length)) := by
  cases kind <;> cases key <;> decide

/-! ## Own accessors of an unchanged object

After the recipe, `produce` calls each own getter in the result once. An object is kept, with its
accessors, when the recipe changed none of its data, every child it reaches is kept, and every
getter returned exactly the value the result holds there: the child itself or a primitive. A
getter that returned a draft handle, or a value that changed, makes the object new, with data
properties that hold the returned values. -/

/-- What one own getter returned: a primitive, a child the result keeps, a child that changed,
or a draft handle, which the result replaces by its value. -/
inductive Returned where
  | primitive
  | keptChild
  | changedChild
  | handle
  deriving DecidableEq, Repr

/-- The getter returned the value the result holds at that slot. -/
def resolvesToItself : Returned → Bool
  | .primitive => true
  | .keptChild => true
  | .changedChild => false
  | .handle => false

/-- The object stays, with its accessors, only if nothing it holds or returns changed. -/
def keeps (dataChanged : Bool) (returned : List Returned) : Bool :=
  !dataChanged && returned.all resolvesToItself

/-- A kept object's live getter returns what the rebuilt object would hold, so keeping it changes
no value a caller reads; a handle never escapes into the result. -/
theorem keeps_iff (dataChanged : Bool) (returned : List Returned) :
    keeps dataChanged returned = true ↔
      dataChanged = false ∧ ∀ r ∈ returned, r = .primitive ∨ r = .keptChild := by
  unfold keeps
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true] at h
    refine ⟨h.1, fun r hr => ?_⟩
    have := h.2 r hr
    cases r <;> simp_all [resolvesToItself]
  · rintro ⟨hd, hr⟩
    simp only [hd, Bool.not_false, Bool.true_and, List.all_eq_true]
    intro r hm
    rcases hr r hm with h | h <;> simp [h, resolvesToItself]

theorem handle_rebuilds (dataChanged : Bool) (returned : List Returned)
    (h : Returned.handle ∈ returned) : keeps dataChanged returned = false := by
  unfold keeps
  cases dataChanged
  · simp only [Bool.not_false, Bool.true_and, List.all_eq_false]
    exact ⟨_, h, by simp [resolvesToItself]⟩
  · rfl

end Reconcile.DraftSurface
