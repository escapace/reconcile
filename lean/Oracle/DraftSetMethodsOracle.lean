import Produce.DraftSetMethods
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `DraftSetMethods` family: what each `Set` method returns under
`DraftSetMethods` for every pair of a draft's members and an operand's keys. -/

namespace Reconcile.DraftSetMethodsOracle

open Reconcile.DraftSetMethods Reconcile.Enumerate Reconcile.Protocol Lean

/-- Every list of distinct values from `a`, `b` and the number 7, whose identities are 0, 1 and 2:
1 + 3 + 6 + 6 lists. -/
private def lists : List (List Nat) := arrangements [0, 1, 2]

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
def run : IO Unit :=
  emitCorpus (lists.flatMap fun members => lists.map (members, ·)) fun (members, keys) =>
    ({ members, keys, union := union id members keys,
       intersection := intersection id members keys,
       difference := difference id members keys,
       symmetricDifference := symmetricDifference id members keys,
       isSubsetOf := isSubsetOf id members keys, isSupersetOf := isSupersetOf id members keys,
       isDisjointFrom := isDisjointFrom id members keys } : Observation)

end Reconcile.DraftSetMethodsOracle
