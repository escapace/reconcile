import Property.PropertyPlacement
import Lean

/-! Oracle for the `PropertyPlacement` family: every pair of own-key orders with the keys that
`PropertyPlacement`'s reference cursor keeps. -/

namespace Reconcile.PropertyPlacementOracle

open Reconcile.PropertyOrder Reconcile.PropertyPlacement Lean

private def arrangements : List Key → List (List Key)
  | [] => [[]]
  | keys => [] :: keys.flatMap fun key =>
      (arrangements (keys.erase key)).map (key :: ·)
termination_by keys => keys.length
decreasing_by
  rename_i h
  exact List.length_erase_of_mem h ▸ Nat.sub_lt (List.length_pos_of_mem h) Nat.one_pos

/-- Own-key orders: an optional integer key, then any arrangement of up to three names, then any
arrangement of up to two symbols. -/
private def ownOrders : List (List Key) :=
  [[], [.index 0]].flatMap fun indices =>
    (arrangements [.name 0, .name 1, .name 2]).flatMap fun names =>
      (arrangements [.symbol 0, .symbol 1]).map fun symbols => indices ++ names ++ symbols

private def encode : Key → Nat
  | .index label => 3 * label
  | .name label => 3 * label + 1
  | .symbol label => 3 * label + 2

private structure Observation where
  current : List Nat
  desired : List Nat
  kept : List Nat
  deriving ToJson

/-- Every pair of own-key orders and the keys the reference cursor keeps. A fixed set is placeable
exactly when it lies within `kept` (`reference_keeps_fixed_iff`), and greedy placement yields the
desired names and symbols (`place_matched`); both are checked here as executable witnesses. -/
def run : IO Unit := do
  let orders := ownOrders
  IO.println (orders.length * orders.length)
  for current in orders do
    for desired in orders do
      let kept := keptKeys desired current
      let names := desired.filter isName
      let symbols := desired.filter isSymbol
      if place (current.filter isName) names (kept.filter isName) != names ||
          place (current.filter isSymbol) symbols (kept.filter isSymbol) != symbols then
        throw (IO.userError "PropertyPlacement witness failed")
      let observation : Observation :=
        { current := current.map encode, desired := desired.map encode, kept := kept.map encode }
      IO.println (toJson observation).compress

end Reconcile.PropertyPlacementOracle
