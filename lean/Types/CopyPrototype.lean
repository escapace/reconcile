import Mathlib.Data.List.Basic

/-!
# Copy prototypes

A copy of an array, `Map`, `Set`, `Date`, `DataView`, `URL`, `URLSearchParams` or Temporal value
is built by its kind's constructor, so it starts on the kind's standard prototype. The prototype
is behavior, not content, so a copy keeps the source's: a subclass instance stays an instance of
its subclass, as class instances and typed arrays already do. Changing a prototype is costly, so
the runtime changes it only when the source's prototype differs from the standard one.

`deserialize` has no class to restore, so it builds every value on its kind's standard prototype.
`serialize` therefore accepts only that prototype and rejects a subclass instance, which would
otherwise come back as an instance of its base kind.
-/

namespace Reconcile.CopyPrototype

/-- The prototype a copy ends with: built on `standard`, then set to the source's prototype when
that differs. -/
def adopt {P : Type} [DecidableEq P] (standard source : P) : P :=
  if source = standard then standard else source

/-- Skipping the change for a standard prototype gives the same result. -/
theorem adopt_eq {P : Type} [DecidableEq P] (standard source : P) :
    adopt standard source = source := by
  unfold adopt
  split_ifs with h
  · exact h.symm
  · rfl

/-- Built-in kinds whose copies the runtime builds by constructor. -/
inductive Kind where
  | array | map | set | date | dataView | url | urlSearchParams | temporal
  deriving DecidableEq, Repr

def kinds : List Kind :=
  [.array, .map, .set, .date, .dataView, .url, .urlSearchParams, .temporal]

/-- Prototypes in the bridge: the kind's standard one or a subclass's. -/
inductive Proto where
  | standard (kind : Kind)
  | subclass (kind : Kind)
  deriving DecidableEq, Repr

/-- Every copy of every kind keeps its source's prototype. -/
theorem copy_keeps (kind : Kind) (source : Proto) :
    adopt (Proto.standard kind) source = source := adopt_eq _ _

/-- Whether `serialize` accepts a value with this prototype. -/
def serializes : Proto → Bool
  | .standard _ => true
  | .subclass _ => false

/-- The prototype `deserialize` gives a value of this kind. -/
def restored (kind : Kind) : Proto := .standard kind

/-- `serialize` accepts a value of a kind exactly when `deserialize` restores its prototype, so
an accepted value round-trips with its prototype and a subclass instance is rejected. -/
theorem serializes_iff_restored (kind : Kind) (source : Proto)
    (h : source = .standard kind ∨ source = .subclass kind) :
    serializes source = true ↔ restored kind = source := by
  rcases h with rfl | rfl <;> simp [serializes, restored]

end Reconcile.CopyPrototype
