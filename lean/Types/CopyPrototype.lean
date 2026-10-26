import Mathlib.Data.List.Basic

/-!
# Copy prototypes

A copy of an array, `Map`, `Set`, `Date`, `DataView`, typed array, `URL`, `URLSearchParams` or
Temporal value is built by its kind's constructor, so it starts on the kind's standard prototype.
The prototype is behavior, not content, so a copy keeps the source's: a subclass instance stays an
instance of its subclass, as class instances already do. Changing a prototype is costly, so
the runtime changes it only when the source's prototype differs from the standard one.

`deserialize` has no class to restore, so it builds every value on its kind's standard prototype.
`serialize` therefore accepts only that prototype and rejects a subclass instance, which would
otherwise come back as an instance of its base kind. A typed array's kind includes its element
type, which its own brand names; given another element type's prototype, it would come back as a
view of that element type over other bytes, so `serialize` rejects it too. A typed array given
`DataView.prototype` is a `DataView` by its chain, as recognition decides, and is accepted.
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

/-- Built-in kinds whose copies the runtime builds by constructor. A typed array's kind carries
its element type, as an index into the runtime's `viewConstructors`. -/
inductive Kind where
  | array | map | set | date | dataView | url | urlSearchParams | temporal
  | typed (element : Nat)
  deriving DecidableEq, Repr

/-- The kinds the bridge builds: `Uint8Array` and `Uint16Array` stand for the typed arrays. -/
def kinds : List Kind :=
  [.array, .map, .set, .date, .dataView, .url, .urlSearchParams, .temporal, .typed 1, .typed 4]

/-- Prototypes in the bridge: a kind's standard one or a subclass's. A value holds its own kind's,
or, for a typed array, another element type's standard one. -/
inductive Proto where
  | standard (kind : Kind)
  | subclass (kind : Kind)
  deriving DecidableEq, Repr

/-- Every copy of every kind keeps its source's prototype. -/
theorem copy_keeps (kind : Kind) (source : Proto) :
    adopt (Proto.standard kind) source = source := adopt_eq _ _

/-- Whether `serialize` accepts a value of `kind` with this prototype: only its own kind's standard
one. -/
def serializes (kind : Kind) : Proto → Bool
  | .standard k => k == kind
  | .subclass _ => false

/-- The prototype `deserialize` gives a value of this kind. -/
def restored (kind : Kind) : Proto := .standard kind

/-- `serialize` accepts a value of a kind exactly when `deserialize` restores its prototype, so
an accepted value round-trips with its prototype and a subclass instance is rejected. -/
theorem serializes_iff_restored (kind : Kind) (source : Proto) :
    serializes kind source = true ↔ restored kind = source := by
  cases source with
  | standard k =>
    simp only [serializes, restored, beq_iff_eq, Proto.standard.injEq]
    exact eq_comm
  | subclass k => simp [serializes, restored]

/-- A `Uint8Array` given `Uint16Array.prototype` is rejected: it would come back as a
`Uint16Array`. -/
example : serializes (.typed 1) (.standard (.typed 4)) = false := by decide

end Reconcile.CopyPrototype
