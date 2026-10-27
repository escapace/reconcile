import Produce.CompactImmutable
import Graph.Construction
import Oracle.Protocol

/-! Oracle for the `CompactImmutable` family: for each bounded case, whose rows have distinct
storages as the runtime's records do, the compact ranked masks (`CompactImmutable.ranked`), which
decode to the reference ranked plans (`ranked_decode`), and the construction schedule of each plan
(`Construction.schedule`), over dependencies one level deep as the runtime's are
(`Construction.schedule_flat`). -/

namespace Reconcile.CompactImmutableOracle

open Lean Reconcile.CompactImmutable Reconcile.Protocol

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
  masks : List (List Bool)
  orders : List (Option (List Nat))
  deriving ToJson

private def bounded (size : Nat) (row : InputRow) : Bool :=
  decide (size ≤ row.proposed) && decide (size ≤ row.storage) && row.children.all (· < size)

/-- Checks the premises of `Problem` (every label reserved, every child a row) and of
`schedule_flat` (every dependency a row without dependencies of its own). -/
private def observe (input : Input) : Except String Observation := do
  let size := input.rows.length
  if !(input.dependencies.all fun row => row.all fun dependency =>
      dependency < size && (input.dependencies[dependency]?.getD []).isEmpty) then
    throw "Compact immutable case has a dependency outside its rows or with dependencies"
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
    let order := fun bits : List Bool =>
      let kept := (List.range size).filter fun i => bits[i]?.getD false
      Reconcile.Construction.schedule (fun i => input.dependencies[i]?.getD [])
        kept.toFinset (List.range size)
    return { input, masks, orders := masks.map order }
  else throw "Invalid child index or non-reserved immutable label"

def run : IO Unit := do
  let cases := (List.range 512).flatMap fun graph => (List.range 8).flatMap fun flags =>
    let rows := (List.range 3).map fun i => {
      proposed := 3 + i, storage := 6 + i, eligible := flags.testBit i, fixed := false
      children := (List.range 3).filter fun j => graph.testBit (i * 3 + j) : InputRow }
    let fixed := rows.zipIdx |>.map fun (row, i) =>
      { row with eligible := true, fixed := flags.testBit i }
    [{ rows, dependencies := [[], [], []] }, { rows := fixed, dependencies := [[1], [], [1]] }]
  let self : InputRow := {
    proposed := 1, storage := 2, eligible := true, fixed := false, children := [0, 0] }
  let impossible : InputRow := {
    proposed := 1, storage := 2, eligible := false, fixed := true, children := [] }
  let boundary : List Input := [{ rows := [], dependencies := [] },
    { rows := [self], dependencies := [[]] }, { rows := [impossible], dependencies := [[]] }]
  emitCheckedCorpus (cases ++ boundary) observe

end Reconcile.CompactImmutableOracle
