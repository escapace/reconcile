import Produce.CompactImmutable
import Graph.Construction
import Lean

/-! Oracle for the `CompactImmutable` family: for each bounded case, whose rows have distinct
storages as the runtime's records do, it checks that the compact ranked masks
(`CompactImmutable.ranked`) decode to the reference ranked plans and schedules construction for
each plan with `Construction.schedule`, over dependencies one level deep as the runtime's are
(`Construction.schedule_flat`). -/

namespace Reconcile.CompactImmutableOracle

open Lean Reconcile.CompactImmutable

private structure InputRow where
  proposed : Nat
  storage : Nat
  eligible : Bool
  fixed : Bool
  children : List Nat
  deriving ToJson

private structure Input where
  rows : List InputRow
  dependencies : List (List Nat)
  deriving ToJson

private structure Observation where
  input : Input
  domains : Reconcile.Policy.Domains
  masks : List (List Bool)
  orders : List (Option (List Nat))
  deriving ToJson

private def bounded (size : Nat) (row : InputRow) : Bool :=
  decide (size ≤ row.proposed) && decide (size ≤ row.storage) && row.children.all (· < size)

private def emit (input : Input) : IO Unit := do
  let size := input.rows.length
  let variableCount := input.rows.countP fun row => row.eligible && !row.fixed
  if size > 64 || variableCount > 12 || input.dependencies.length != size ||
      !(input.dependencies.all fun row => row.length ≤ 128 && row.all (· < size)) ||
      !(input.rows.all fun row => row.children.length ≤ 128) then
    throw (IO.userError "Compact immutable fixture exceeds finite bridge bounds")
  if !(input.dependencies.all fun row => row.all fun dependency =>
      (input.dependencies[dependency]?.getD []).isEmpty) then
    throw (IO.userError "Compact immutable fixture has a dependency with dependencies")
  if checked : input.rows.all (bounded size) then
    have bounds (i : Fin size) : size ≤ input.rows[i.val].proposed ∧
        size ≤ input.rows[i.val].storage ∧
        ∀ child ∈ input.rows[i.val].children, child < size := by
      simpa [bounded, List.all_eq_true, and_assoc] using
        (List.all_eq_true.mp checked input.rows[i.val] (List.getElem_mem i.isLt))
    let p : Problem size := {
      row := fun i => {
        proposed := input.rows[i.val].proposed
        storage := input.rows[i.val].storage
        eligible := input.rows[i.val].eligible
        fixed := input.rows[i.val].fixed
        children := input.rows[i.val].children.attach.map fun child =>
          ⟨child.val, (bounds i).2.2 child.val child.property⟩ }
      proposedReserved := fun i => (bounds i).1
      storageReserved := fun i => (bounds i).2.1 }
    let masks := ranked p
    if masks.map (decode p (List.finRange size)) != Reconcile.Policy.rankedPlans (domains p) then
      throw (IO.userError "Compact and decoded ranked streams differ")
    let order := fun bits : List Bool =>
      let kept := (List.range size).filter fun i => bits[i]?.getD false
      Reconcile.Construction.schedule (fun i => input.dependencies[i]?.getD [])
        kept.toFinset (List.range size)
    let observation : Observation := { input, domains := domains p, masks, orders := masks.map order }
    IO.println (toJson observation).compress
  else throw (IO.userError "Invalid child index or non-reserved immutable label")

private def emitCorpus : IO Unit := do
  IO.println (8192 + 3)
  for graph in List.range 512 do
    for flags in List.range 8 do
      let rows := (List.range 3).map fun i => {
        proposed := 3 + i, storage := 6 + i, eligible := flags.testBit i, fixed := false
        children := (List.range 3).filter fun j => graph.testBit (i * 3 + j) : InputRow }
      emit { rows, dependencies := [[], [], []] }
      let fixed := rows.zipIdx |>.map fun (row, i) =>
        { row with eligible := true, fixed := flags.testBit i }
      emit { rows := fixed, dependencies := [[1], [], [1]] }
  emit { rows := [], dependencies := [] }
  let self : InputRow := {
    proposed := 1, storage := 2, eligible := true, fixed := false, children := [0, 0] }
  emit { rows := [self], dependencies := [[]] }
  let impossible : InputRow := {
    proposed := 1, storage := 2, eligible := false, fixed := true, children := [] }
  emit { rows := [impossible], dependencies := [[]] }

def run : IO Unit := emitCorpus

end Reconcile.CompactImmutableOracle
