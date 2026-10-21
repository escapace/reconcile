import Mathlib.Data.List.Nodup

/-!
# Draft iteration

A `Map` draft reads its original until the first change and a working copy afterwards. Iterating
the draft makes the working copy first and walks it with the copy's native iterator, so every
later write through the draft changes the collection being walked, as on a native `Map`, and
the iteration sees exactly the draft's contents. Making the copy is not a change: an iteration
that changes nothing leaves the result the original, which `produce` keeps whenever the entries
end up equal to the original's.

Entries are an insertion-ordered list of key and value pairs. A `Set` is the case where each
value is its key. A `Set` method that returns a set, such as `union`, gives each object member of
the draft as its draft (`DraftSetMethods`).
-/

namespace Reconcile.DraftIteration

/-- A draft: the original entries, the working copy once made, and whether a write changed it. -/
structure Draft where
  base : List (Nat × Nat)
  copy : Option (List (Nat × Nat))
  modified : Bool
  deriving DecidableEq, Repr

/-- The entries the draft holds now. -/
def source (d : Draft) : List (Nat × Nat) := d.copy.getD d.base

/-- Makes the working copy if there is none. -/
def prepare (d : Draft) : Draft := { d with copy := some (source d) }

/-- Native `Map.prototype.set`: replaces the value in place or appends a new entry. -/
def setEntry (k v : Nat) (entries : List (Nat × Nat)) : List (Nat × Nat) :=
  if entries.any (·.1 == k) then entries.map fun e => if e.1 == k then (k, v) else e
  else entries ++ [(k, v)]

/-- Native `Map.prototype.delete`. -/
def deleteEntry (k : Nat) (entries : List (Nat × Nat)) : List (Nat × Nat) :=
  entries.filter (·.1 != k)

/-- A draft write: an equal value or a missing key changes nothing; otherwise the copy changes. -/
def set (k v : Nat) (d : Draft) : Draft :=
  if (k, v) ∈ source d then d
  else let p := prepare d; { p with copy := some (setEntry k v (source p)), modified := true }

def delete (k : Nat) (d : Draft) : Draft :=
  if (source d).any (·.1 == k) then
    let p := prepare d; { p with copy := some (deleteEntry k (source p)), modified := true }
  else d

/-- Starting an iteration makes the working copy and walks it. -/
def iterate (d : Draft) : Draft × List (Nat × Nat) := (prepare d, source (prepare d))

/-- Whether the result is the original collection: its entries end up equal to the original's,
in order, so an undone change also keeps it. -/
def kept (d : Draft) : Bool := source d == d.base

theorem source_prepare (d : Draft) : source (prepare d) = source d := by
  simp [source, prepare]

/-- An iteration walks exactly the draft's current entries. -/
theorem iterate_entries (d : Draft) : (iterate d).2 = source d := source_prepare d

/-- Iterating is not a change: the draft holds the same entries, and the result keeps the
original exactly when it did before. -/
theorem iterate_kept (d : Draft) :
    source (iterate d).1 = source d ∧ kept (iterate d).1 = kept d := by
  refine ⟨source_prepare d, ?_⟩
  change (source (prepare d) == (prepare d).base) = (source d == d.base)
  rw [source_prepare]
  rfl

/-- After an iteration starts, a write changes the copy the iterator walks: the copy exists and
the write replaces it in place, as a native `Map` would change during its own iteration. -/
theorem write_after_iterate (d : Draft) (k v : Nat) :
    ((iterate d).1.copy).isSome ∧
      (set k v (iterate d).1).copy =
        if (k, v) ∈ source d then some (source d) else some (setEntry k v (source d)) := by
  constructor
  · simp [iterate, prepare]
  · change (set k v (prepare d)).copy = _
    unfold set
    rw [source_prepare]
    by_cases h : (k, v) ∈ source d
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      simp [prepare, source]

/-- A draft no write changed keeps the original collection. -/
theorem kept_untouched (base : List (Nat × Nat)) : kept ⟨base, none, false⟩ = true := by
  simp [kept, source]

/-- Each object has one draft, so mapping members to their drafts is injective, and the members a
`Set` combination returns stay distinct when each object member is replaced by its draft. -/
theorem drafted_nodup {α β : Type} (draft : α → β) (injective : Function.Injective draft)
    (members : List α) (distinct : members.Nodup) : (members.map draft).Nodup :=
  distinct.map injective

end Reconcile.DraftIteration
