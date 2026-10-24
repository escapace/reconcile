import Produce.Immutable
import Lean

/-! Oracle for the `Contract` family. It runs each graph in `reuse-fixtures.json` through
`Policy.select` and the verified immutable core (`Immutable.publish`), checks the compiler facts,
the readback and the unchanged input frame, and reports the selected identities, values and edges.
A wrapper and its raw object are one node, as identity restoration registers them.
-/

namespace Reconcile.ContractOracle

open Lean

structure ReuseFixture where
  name : String
  before : Array Nat
  after : Array Nat
  children : Array (Array Nat)
  undo : Bool
  deriving FromJson

structure ReuseObservation where
  name : String
  identities : Array Nat
  values : Array Nat
  edges : Array (Array Nat)
  deriving ToJson

private def fixtureNode (value : Nat) (children : Array Nat) : Node Nat Nat :=
  .plainObject ⟨0⟩ (⟨⟨0⟩, .atom value⟩ ::
    children.toList.zipIdx.map fun (child, index) => ⟨⟨index + 1⟩, .ref child⟩)

/-- The verified core on a fixture whose wrappers are already merged into their raw objects:
the selected identities, values and edges of each node, by node index. -/
private def runCanonical (name : String) (before after : Array Nat) (children : Array (Array Nat)) :
    Except String (Array Nat × Array Nat × Array (Array Nat)) := do
  let size := before.size
  if size = 0 || after.size != size || children.size != size then
    throw s!"{name}: mismatched fixture sizes"
  if children.any (·.any (· >= size)) then
    throw s!"{name}: dangling reference"
  let ids := List.range size
  let records := ids.map fun i => (i, fixtureNode after[i]! children[i]!)
  let before' := publishRecords id (fun _ => id)
    (ids.map fun i => (i, fixtureNode before[i]! children[i]!)) ∅
  let domains : Policy.Domains := ids.map fun i =>
    let fresh : Policy.Choice := ⟨i + size, i + size, false, []⟩
    if before[i]! = after[i]! then
      [⟨i, i, true, children[i]!.toList.map fun child => ⟨child, child⟩⟩, fresh]
    else [fresh]
  let some plan := Policy.select domains
    | throw s!"{name}: no feasible assignment"
  if hzero : plan.length = 0 then
    throw s!"{name}: empty assignment"
  else
    if plan.length != size then
      throw s!"{name}: incomplete assignment"
    let finite := fun n => (⟨n % plan.length, Nat.mod_lt _ (Nat.pos_of_ne_zero hzero)⟩ : Fin plan.length)
    let finiteRecords := (List.finRange plan.length).map fun i =>
      (i, (fixtureNode after[i.val]! children[i.val]!).remap finite id)
    let input : Immutable.Input Nat plan := {
      source := publishRecords id (fun _ => id) finiteRecords ∅
      before := before'
      proposed := Fin.val
      fresh := fun i => i.val + size
      storage := id
      proto := fun _ => id
      records := finiteRecords
    }
    if !Immutable.checkCompiled input domains then
      throw s!"{name}: invalid compiler facts"
    let result := Immutable.publish input
    let image := fun i => Immutable.image plan (finite i)
    if !checkPublication image (fun _ => id) records result then
      throw s!"{name}: immutable core failed readback"
    if ids.any (fun r => result.lookup r != before'.lookup r) then
      throw s!"{name}: input frame changed"
    let mut values := #[]
    let mut edges := #[]
    for i in ids do
      match result.lookup (image i) with
      | some (.plainObject _ (⟨_, .atom value⟩ :: rest)) =>
        values := values.push value
        let mut refs := #[]
        for ⟨_, child⟩ in rest do
          match child with
          | .ref r => refs := refs.push r
          | _ => throw "unexpected atom child"
        edges := edges.push refs
      | _ => throw "missing output payload"
    return ((ids.map image).toArray, values, edges)

/-- Runs the core on the fixture's graph. A kept node is reported at its position, and a new node
as the first position that holds it, as the runtime labels them. -/
private def runFixture (fixture : ReuseFixture) : Except String ReuseObservation := do
  let size := fixture.before.size
  let canon := fun (r : Nat) => r
  let ids := List.range size
  let raws := (ids.filter fun i => canon i = i).toArray
  let position := fun r => (raws.findIdx? (· = canon r)).getD 0
  let first := fun r => (ids.find? (fun j => canon j = canon r)).getD r
  let pick := fun (values : Array Nat) => raws.map fun r => values[r]!
  let children := raws.map fun r => fixture.children[r]!.map position
  let (images, values, edges) ←
    runCanonical fixture.name (pick fixture.before) (pick fixture.after) children
  let count := raws.size
  -- A kept node keeps the view a position held; a new one is labelled by its first position.
  let present := fun (original : Nat) (identity : Nat) =>
    if identity < count then original else size + first original
  return {
    name := fixture.name
    identities := (ids.map fun i => present i images[position i]!).toArray
    values := (ids.map fun i => values[position i]!).toArray
    edges := (ids.map fun i =>
      if canon i ≠ i then #[]
      else (fixture.children[i]!.zip edges[position i]!).map fun (c, r) => present c r).toArray
  }

def run (args : List String) : IO UInt32 := do
  let path := args.headD "lean/fixtures/reuse-fixtures.json"
  let content ← IO.FS.readFile path
  let parsed := Json.parse content >>= fromJson? (α := Array ReuseFixture)
  match parsed >>= (·.mapM runFixture) with
  | .error error => IO.eprintln error; return 1
  | .ok observations => IO.println (toJson observations).compress; return 0

end Reconcile.ContractOracle
