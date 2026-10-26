import Graph.SeededRequirements
import Lean

/-! Oracle for the `SeededRequirements` family: the `SeededRequirements` closure over all
three-node graphs and short seed words plus larger boundary cases, or over the native-compiled
graphs in a fixture file. -/

namespace Reconcile.SeededRequirementsOracle

open Reconcile.SeededRequirements Reconcile.RequirementPropagation Lean

private def wordsUpTo : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | depth + 1, letters =>
    [] :: letters.flatMap (fun letter => (wordsUpTo depth letters).map (letter :: ·))

private structure Observation where
  parents : List (List Nat)
  trimmed : List (List Nat)
  seeds : List Nat
  trace : List Nat
  oldScans : Nat
  newScans : Nat
  deriving ToJson

private def emit (parents : List (List Nat)) (seeds : List Nat) : IO Unit := do
  let successors := fun fact => parents[fact]?.getD []
  let filtered := trim seeds.toFinset successors
  let before := run successors parents.length (start ∅ seeds)
  let after := run filtered parents.length (start ∅ seeds)
  let oldScans := scans successors before.processed
  let newScans := scans filtered after.processed
  if before.processed != after.processed || before.admitted != after.admitted ||
      !before.pending.isEmpty || !after.pending.isEmpty || newScans > oldScans then
    throw (IO.userError "Seeded-requirements model witness failed")
  let observation : Observation :=
    { parents, trimmed := (List.range parents.length).map filtered, seeds,
      trace := before.processed, oldScans, newScans }
  IO.println (toJson observation).compress

/-- All three-node directed graphs, seed words of length at most three and
both ordinary and duplicated rows; larger boundary families follow. -/
private def emitCorpus : IO Unit := do
  let seeds := wordsUpTo 3 (List.range 3)
  IO.println (512 * seeds.length * 2 + 6)
  for mask in List.range 512 do
    let parents := (List.range 3).map fun child =>
      (List.range 3).filter fun parent => mask.testBit (child * 3 + parent)
    for seed in seeds do
      emit parents seed
      emit (parents.map fun row => row ++ row) seed
  emit [] []
  let ring := (List.range 64).map fun child => [(child + 1) % 64]
  emit ring [0]
  emit ring []
  emit ring (List.range 64)
  let fanout := (List.range 64).map fun child =>
    if child = 0 then (List.range 64).drop 1 else []
  emit fanout [0, 0]
  emit fanout (List.range 64)

/-- Emits the exhaustive fixed corpus. -/
def run : IO Unit := emitCorpus

end Reconcile.SeededRequirementsOracle
