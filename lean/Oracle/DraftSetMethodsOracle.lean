import Produce.DraftSetMethods
import Lean

/-! Oracle for the `DraftSetMethods` family: what each `Set` method returns under
`DraftSetMethods` for every pair of a draft's members and an operand's keys. -/

namespace Reconcile.DraftSetMethodsOracle

open Reconcile.DraftSetMethods Lean

/-- Every list of distinct values from `a`, `b` and the number 7, whose identities are 0, 1 and 2:
1 + 3 + 6 + 6 lists. -/
private def lists : List (List Nat) :=
  let values := [0, 1, 2]
  [[]] ++ values.map (fun a => [a]) ++
    (values.flatMap fun a => values.filterMap fun b => if a ≠ b then some [a, b] else none) ++
    (values.flatMap fun a => values.flatMap fun b => values.filterMap fun c =>
      if a ≠ b ∧ a ≠ c ∧ b ≠ c then some [a, b, c] else none)

private structure Observation where
  members : List Nat
  keys : List Nat
  union : List Nat
  intersection : List Nat
  difference : List Nat
  symmetricDifference : List Nat
  isSubsetOf : Bool
  isSupersetOf : Bool
  isDisjointFrom : Bool
  deriving ToJson

/-- Every pair of a draft's members and an operand's keys, with what each method returns. -/
def run : IO Unit := do
  IO.println (lists.length * lists.length)
  for members in lists do
    for keys in lists do
      let row : Observation :=
        { members, keys, union := union id members keys,
          intersection := intersection id members keys,
          difference := difference id members keys,
          symmetricDifference := symmetricDifference id members keys,
          isSubsetOf := isSubsetOf id members keys, isSupersetOf := isSupersetOf id members keys,
          isDisjointFrom := isDisjointFrom id members keys }
      IO.println (toJson row).compress

end Reconcile.DraftSetMethodsOracle
