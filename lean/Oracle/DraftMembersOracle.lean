import Produce.DraftMembers
import Lean

/-! Oracle for the `DraftMembers` family: what `includes`, `indexOf` and `lastIndexOf` return under
`DraftMembers` on the array `[a, b, a, 7]` for every searched value. -/

namespace Reconcile.DraftMembersOracle

open Reconcile.DraftMembers Lean

/-- The array `[a, b, a, 7]` by identity: objects `a` and `b` are 0 and 1, the number 7 is 2. -/
private def elements : List Nat := [0, 1, 0, 2]

/-- Searched values: `a` or `b` as the object, its draft or its Vue proxy, an unrelated object
(9), the number 7, and a number the array does not hold (8). Each form has its object's identity. -/
private def queries : List (String × Nat) :=
  [("a", 0), ("a draft", 0), ("a proxy", 0), ("b", 1), ("b draft", 1), ("b proxy", 1),
    ("other", 9), ("7", 2), ("8", 8)]

private structure Observation where
  query : String
  includes : Bool
  indexOf : Int
  lastIndexOf : Int
  deriving ToJson

private def position : Option Nat → Int
  | some n => n
  | none => -1

/-- Every searched value with what `includes`, `indexOf` and `lastIndexOf` return. -/
def run : IO Unit := do
  IO.println queries.length
  for (query, key) in queries do
    let row : Observation :=
      { query, includes := includes id elements key,
        indexOf := position (indexOf id elements key),
        lastIndexOf := position (lastIndexOf id elements key) }
    IO.println (toJson row).compress

end Reconcile.DraftMembersOracle
