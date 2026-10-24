import Produce.DraftMembers
import Lean

/-! Oracle for the `DraftMembers` family: what `includes`, `indexOf` and `lastIndexOf` return under
`DraftMembers` for every searched value, on the plain array draft `[a, b, a, 7]`, with every
element read before the search and with the array searched before any element is read. -/

namespace Reconcile.DraftMembersOracle

open Reconcile.DraftMembers Lean

/-- Values by number: objects `a` and `b`, the number 7, the drafts of `a` and `b`, the number 8
and an unrelated object. -/
private def queries : List (String × Nat) :=
  [("a", 0), ("a draft", 6), ("b", 1), ("b draft", 7), ("other", 9), ("7", 2), ("8", 8)]

/-- The object each value is: a draft's is the object it drafts. -/
private def base : Nat → Nat
  | 6 => 0
  | 7 => 1
  | n => n

/-- A key when the values in `drafted` have drafts: the base of a drafted value, and any other
value itself. -/
private def keyOf (drafted : List Nat) (v : Nat) : Nat :=
  if v ∈ drafted then base v else v

private structure Scenario where
  name : String
  elements : List Nat
  /-- The values drafted before the search, and after it has read every element. -/
  before : List Nat
  after : List Nat

private def scenarios : List Scenario :=
  [{ name := "plain", elements := [0, 1, 0, 2], before := [0, 1, 6, 7], after := [0, 1, 6, 7] },
    { name := "plain, searched first", elements := [0, 1, 0, 2], before := [6, 7],
      after := [0, 1, 6, 7] }]

private structure Observation where
  scenario : String
  query : String
  includes : Bool
  indexOf : Int
  lastIndexOf : Int
  deriving ToJson

private def position : Option Nat → Int
  | some n => n
  | none => -1

/-- Every searched value in every scenario with what `includes`, `indexOf` and `lastIndexOf`
return. -/
def run : IO Unit := do
  IO.println (scenarios.length * queries.length)
  for scenario in scenarios do
    for (query, key) in queries do
      let before := keyOf scenario.before
      let held := keyOf scenario.after
      let targets := fun x => [before x]
      let elements := scenario.elements
      let row : Observation :=
        { scenario := scenario.name, query, includes := includesBy held targets elements key,
          indexOf := position (indexOfBy held targets elements key),
          lastIndexOf := position (lastIndexOfBy held targets elements key) }
      IO.println (toJson row).compress

end Reconcile.DraftMembersOracle
