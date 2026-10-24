import Produce.DraftMembers
import Lean

/-! Oracle for the `DraftMembers` family: what `includes`, `indexOf` and `lastIndexOf` return under
`DraftMembers` for every searched value, on four array drafts: plain `[a, b, a, 7]`; plain
`[reactive(a), b, a, 7]` whose Vue proxy is drafted before the search, and the same array searched
before any element is read; and Vue reactive `[a, b, a, 7]`. -/

namespace Reconcile.DraftMembersOracle

open Reconcile.DraftMembers Lean

/-- Values by number: objects `a` and `b`, the number 7, Vue proxies `reactive(a)`,
`shallowReactive(a)` and `reactive(b)`, the drafts of `a` and `b`, the number 8 and an unrelated
object. -/
private def queries : List (String × Nat) :=
  [("a", 0), ("a draft", 6), ("a proxy", 3), ("a shallow proxy", 4), ("b", 1), ("b draft", 7),
    ("b proxy", 5), ("other", 9), ("7", 2), ("8", 8)]

/-- The raw object of each value; a draft's is that of the object it drafts. -/
private def storage : Nat → Nat
  | 3 | 4 | 6 => 0
  | 5 | 7 => 1
  | n => n

/-- A key when the values in `drafted` have drafts: the storage of a drafted value, and any other
value itself. -/
private def keyOf (drafted : List Nat) (v : Nat) : Nat :=
  if v ∈ drafted then storage v else v

private structure Scenario where
  name : String
  elements : List Nat
  /-- The values drafted before the search, and after it has read every element. -/
  before : List Nat
  after : List Nat
  vue : Bool

private def scenarios : List Scenario :=
  [{ name := "plain", elements := [0, 1, 0, 2], before := [0, 1, 6, 7], after := [0, 1, 6, 7],
      vue := false },
    { name := "plain, proxy drafted first", elements := [3, 1, 0, 2], before := [0, 1, 3, 6, 7],
      after := [0, 1, 3, 6, 7], vue := false },
    { name := "plain, searched first", elements := [3, 1, 0, 2], before := [6, 7],
      after := [0, 1, 3, 6, 7], vue := false },
    { name := "vue", elements := [0, 1, 0, 2], before := [0, 1, 6, 7], after := [0, 1, 6, 7],
      vue := true }]

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
      let after := keyOf scenario.after
      let held := if scenario.vue then storage ∘ after else after
      let targets := if scenario.vue then fun x => [storage (before x)]
        else plainTargets before storage
      let elements := scenario.elements
      let row : Observation :=
        { scenario := scenario.name, query, includes := includesBy held targets elements key,
          indexOf := position (indexOfBy held targets elements key),
          lastIndexOf := position (lastIndexOfBy held targets elements key) }
      IO.println (toJson row).compress

end Reconcile.DraftMembersOracle
