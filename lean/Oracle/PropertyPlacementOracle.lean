import Property.PropertyPlacement
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `PropertyPlacement` family: every pair of own-key orders with the keys that
`PropertyPlacement`'s reference cursor keeps. -/

namespace Reconcile.PropertyPlacementOracle

open Reconcile.PropertyOrder Reconcile.PropertyPlacement Reconcile.Enumerate Reconcile.Protocol
  Lean

/-- Own-key orders: an optional integer key, then any arrangement of up to three names, then any
arrangement of up to two symbols. -/
private def ownOrders : List (List Key) :=
  [[], [.index 0]].flatMap fun indices =>
    (arrangements [.name 0, .name 1, .name 2]).flatMap fun names =>
      (arrangements [.symbol 0, .symbol 1]).map fun symbols => indices ++ names ++ symbols

private structure Observation where
  current : List Nat
  desired : List Nat
  kept : List Nat
  deriving ToJson

/-- Every pair of own-key orders and the keys the reference cursor keeps. Each order lists its
integer key, names and symbols in that order and without repeats, as `reference_keeps_fixed_iff`
requires: a fixed set is placeable exactly when it lies within `kept`, and greedy placement then
yields the desired names and symbols (`place_matched`). -/
def run : IO Unit :=
  emitCorpus (ownOrders.flatMap fun current => ownOrders.map (current, ·)) fun (current, desired) =>
    ({ current := current.map keyCode, desired := desired.map keyCode
       kept := (keptKeys desired current).map keyCode } : Observation)

end Reconcile.PropertyPlacementOracle
