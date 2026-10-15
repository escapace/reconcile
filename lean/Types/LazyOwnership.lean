import Std

/- Representation refinement only: no native observations or selection changes. -/
namespace Reconcile.LazyOwnership

abbrev Table := Nat → Option Nat

def lookup (table : Option Table) : Table := table.getD (fun _ => none)

def put (table : Option Table) (key value : Nat) : Option Table :=
  some (fun query => if query = key then some value else lookup table query)

theorem absent_is_empty (key : Nat) : lookup none key = none := rfl

theorem present_lookup (table : Table) (key : Nat) :
    lookup (some table) key = table key := rfl

theorem put_refines_eager (table : Option Table) (key value query : Nat) :
    lookup (put table key value) query =
      (if query = key then some value else lookup table query) := rfl

def applyWrites (table : Option Table) (writes : List (Nat × Nat)) : Option Table :=
  writes.foldl (fun current pair => put current pair.1 pair.2) table

theorem same_lookup_after_writes (left right : Option Table)
    (same : lookup left = lookup right) (writes : List (Nat × Nat)) :
    lookup (applyWrites left writes) = lookup (applyWrites right writes) := by
  induction writes generalizing left right with
  | nil => exact same
  | cons pair rest ih =>
    apply ih
    funext query
    simp only [put_refines_eager]
    rw [same]

theorem lazy_eager_equivalent (writes : List (Nat × Nat)) :
    lookup (applyWrites none writes) =
      lookup (applyWrites (some (fun _ => none)) writes) :=
  same_lookup_after_writes none (some (fun _ => none)) rfl writes

example : lookup (applyWrites none [(1, 7), (2, 8), (1, 9)]) 1 = some 9 := by decide
example : lookup (applyWrites none [(1, 7)]) 2 = none := by decide

/-- A missing construction response falls back to the already selected target. -/
theorem omit_identity_response (target : Nat) :
    (none : Option Nat).getD target = (some target).getD target := rfl

end Reconcile.LazyOwnership
