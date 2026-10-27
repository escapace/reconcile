import Produce.Immutable
import Oracle.Protocol

/-! Oracle for the `Contract` family. It runs each graph its bridge sends, those of
`reuse-fixtures.json`, through the head of `Policy.rankedPlans` and the verified immutable core
(`Immutable.publishFresh`), and reports the selected identities, values and edges. It checks the
compiler facts with `checkCompiled`, and checks the readback and the unchanged input frame too: no
theorem derives `Compiled`, which `selected_published` needs, from `checkCompiled`, and none
states the frame. -/

namespace Reconcile.ContractOracle

open Lean

structure ReuseFixture where
  name : String
  before : Array Nat
  after : Array Nat
  children : Array (Array Nat)
  deriving FromJson

structure ReuseObservation where
  identities : Array Nat
  values : Array Nat
  edges : Array (Array Nat)
  deriving ToJson

private def fixtureNode (value : Nat) (children : Array Nat) : Node Nat Nat :=
  .plainObject ⟨0⟩ (⟨⟨0⟩, .atom value⟩ ::
    children.toList.zipIdx.map fun (child, index) => ⟨⟨index + 1⟩, .ref child⟩)

/-- The verified core on a fixture graph: the selected identities, values and edges of each node,
by node index. -/
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
  let some plan := (Policy.rankedPlans domains).head?
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
    let survivors := Immutable.survivors plan
    let result := Immutable.publishFresh survivors input.proposed input.fresh input.proto
      input.records input.before
    let image := fun i => Immutable.reuseImage survivors input.proposed input.fresh (finite i)
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
as the node count plus its position, as the runtime labels them. -/
private def runFixture (fixture : ReuseFixture) : Except String ReuseObservation := do
  let size := fixture.before.size
  let (images, values, edges) ←
    runCanonical fixture.name fixture.before fixture.after fixture.children
  let present := fun (original identity : Nat) =>
    if identity < size then original else size + original
  let ids := List.range size
  return {
    identities := (ids.map fun i => present i images[i]!).toArray
    values := (ids.map fun i => values[i]!).toArray
    edges := (ids.map fun i =>
      (fixture.children[i]!.zip edges[i]!).map fun (c, r) => present c r).toArray
  }

def run (input : String) : IO Unit := Protocol.serveArray input runFixture

end Reconcile.ContractOracle
