import Graph.SeededRequirements
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `SeededRequirements` family: the `SeededRequirements` closure over all
three-node graphs and short seed words plus larger boundary cases. -/

namespace Reconcile.SeededRequirementsOracle

open Reconcile.SeededRequirements Reconcile.RequirementPropagation Reconcile.Enumerate
  Reconcile.Protocol Lean

private structure Observation where
  parents : List (List Nat)
  trimmed : List (List Nat)
  seeds : List Nat
  trace : List Nat
  oldScans : Nat
  newScans : Nat
  deriving ToJson

/-- The closure of `seeds` over `parents`, whose facts are its row indices, which `parents.length`
steps drain (`run_drains`). The trimmed rows close to the same trace (`run_eq`) with no more scans
(`scans_le`). -/
private def observe : List (List Nat) × List Nat → Observation
  | (parents, seeds) =>
    let successors := fun fact => parents[fact]?.getD []
    let filtered := trim seeds.toFinset successors
    let trace := (run successors parents.length (start ∅ seeds)).processed
    { parents, trimmed := (List.range parents.length).map filtered, seeds, trace,
      oldScans := scans successors trace, newScans := scans filtered trace }

/-- Emits the exhaustive fixed corpus: all three-node directed graphs, seed words of length at
most three and both ordinary and duplicated rows; larger boundary families follow. -/
def run : IO Unit := do
  let graphs := (List.range 512).map fun mask => (List.range 3).map fun child =>
    (List.range 3).filter fun parent => mask.testBit (child * 3 + parent)
  let ring := (List.range 64).map fun child => [(child + 1) % 64]
  let fanout := (List.range 64).map fun child =>
    if child = 0 then (List.range 64).drop 1 else []
  emitCorpus ((graphs.flatMap fun parents => (wordsUpTo 3 (List.range 3)).flatMap fun seeds =>
      [(parents, seeds), (parents.map fun row => row ++ row, seeds)]) ++
    [([], []), (ring, [0]), (ring, []), (ring, List.range 64), (fanout, [0, 0]),
      (fanout, List.range 64)]) observe

end Reconcile.SeededRequirementsOracle
