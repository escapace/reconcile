import Produce.DraftMembers
import Lean

/-! Oracle for the `DraftMembers` family: what `includes`, `indexOf` and `lastIndexOf` return under
`DraftMembers` for every searched value, on three array drafts: plain `[a, b, a, 7]`, plain
`[reactive(a), b, a, 7]` whose Vue proxy is drafted before `a`, and Vue reactive `[a, b, a, 7]`. -/

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

private structure Scenario where
  name : String
  elements : List Nat
  held : Nat → Nat
  targets : Nat → List Nat

/-- The base of each draft: `a`'s draft is made from `a`, or from `reactive(a)` when the proxy is
drafted first, and `a` and the proxy then share it; every other value is itself. -/
private def baseOf (proxyFirst : Bool) : Nat → Nat
  | 0 | 6 => if proxyFirst then 3 else 0
  | 7 => 1
  | n => n

private def scenarios : List Scenario :=
  [{ name := "plain", elements := [0, 1, 0, 2], held := baseOf false,
      targets := plainTargets (baseOf false) storage },
    { name := "plain, proxy drafted first", elements := [3, 1, 0, 2], held := baseOf true,
      targets := plainTargets (baseOf true) storage },
    { name := "vue", elements := [0, 1, 0, 2], held := storage ∘ baseOf false,
      targets := fun x => [storage (baseOf false x)] }]

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
      let { name, elements, held, targets } := scenario
      let row : Observation :=
        { scenario := name, query, includes := includesBy held targets elements key,
          indexOf := position (indexOfBy held targets elements key),
          lastIndexOf := position (lastIndexOfBy held targets elements key) }
      IO.println (toJson row).compress

end Reconcile.DraftMembersOracle
