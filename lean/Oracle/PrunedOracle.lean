import Reconcile.PrunedReconcile
import Graph.GraphPolicy
import Lean

/-! Oracle for the `Pruned` family: a differential runner for identical-occupant pruning
(`PrunedReconcile`) over the finite plain-object graphs in `pruned-fixtures.json`. -/

namespace Reconcile.PrunedOracle

open Lean

/-- A next node: pinned to a current index (the object at its own slot), a shared current
    leaf placed at another slot, or captured with a value, next children and an optional
    positional occupant. -/
structure NextNode where
  pinned : Option Nat := none
  shared : Option Nat := none
  value : Option Nat := none
  children : Option (Array Nat) := none
  occupant : Option Nat := none
  deriving FromJson, Inhabited

structure Fixture where
  name : String
  before : Array Nat
  children : Array (Array Nat)
  nodes : Array NextNode
  deriving FromJson

structure Observation where
  name : String
  identities : Array Nat
  values : Array Nat
  edges : Array (Array Nat)
  deriving ToJson

private def fixtureNode (value : Nat) (children : List Nat) : Node Nat Nat :=
  .plainObject ⟨0⟩ (⟨⟨0⟩, .atom value⟩ ::
    children.zipIdx.map fun (child, index) => ⟨⟨index + 1⟩, .ref child⟩)

/-- Current ids are `0 ..< size`; captured next node `i` is `size + i`; its fresh choice is
    `2 * size + i`. A pinned next node is its current id. Objects reachable from pinned
    occupants are protected: no captured node may retain one, and a shared current leaf
    inside that closure is pinned to itself. -/
private partial def closure (children : Array (Array Nat)) (roots : List Nat) : List Nat :=
  let rec go (pending : List Nat) (seen : List Nat) : List Nat :=
    match pending with
    | [] => seen
    | id :: rest =>
      if seen.contains id then go rest seen
      else go (rest ++ children[id]!.toList) (id :: seen)
  go roots []

private def runFixture (fixture : Fixture) : Except String Observation := do
  let size := fixture.before.size
  if size = 0 || fixture.children.size != size || fixture.nodes.size = 0 then
    throw s!"{fixture.name}: mismatched fixture sizes"
  if fixture.children.any (·.any (· >= size)) then
    throw s!"{fixture.name}: dangling current reference"
  let count := fixture.nodes.size
  if fixture.nodes[0]!.pinned.isSome then
    throw s!"{fixture.name}: pinned root"
  let pinnedTargets := fixture.nodes.toList.filterMap (·.pinned)
  for node in fixture.nodes do
    if (node.children.getD #[]).any (· >= count) then
      throw s!"{fixture.name}: dangling next reference"
    if let some k := node.pinned then
      if k >= size then throw s!"{fixture.name}: dangling pinned reference"
    if let some k := node.shared then
      if k >= size then throw s!"{fixture.name}: dangling shared reference"
      if k = 0 || fixture.children[k]!.size != 0 then
        throw s!"{fixture.name}: shared node is not a leaf"
  let protected_ := closure fixture.children pinnedTargets
  -- A shared leaf inside the protected closure is pinned to itself.
  -- A pinned subtree that reaches the current root is captured by the runtime instead;
  -- fixtures stay inside the pinned contract. A shared leaf inside the protected closure
  -- is pinned to itself.
  if protected_.contains 0 then throw s!"{fixture.name}: pinned subtree reaches the root"
  let pinnedOf (node : NextNode) : Option Nat :=
    match node.pinned, node.shared with
    | some k, _ => some k
    | none, some k => if protected_.contains k then some k else none
    | none, none => none
  let ids := List.range size
  let before : Heap Nat Nat := publishRecords id (fun _ => id)
    (ids.map fun i => (i, fixtureNode fixture.before[i]! fixture.children[i]!.toList)) ∅
  let identityOf (plan : Policy.Plan) (j : Nat) : Nat :=
    match pinnedOf fixture.nodes[j]! with
    | some k => k
    | none =>
      let captured := (List.range j).countP fun i => (pinnedOf fixture.nodes[i]!).isNone
      (plan[captured]?).map Policy.Choice.identity |>.getD (2 * size + j)
  let capturedIndices := (List.range count).filter fun i => (pinnedOf fixture.nodes[i]!).isNone
  let domains : Policy.Domains := capturedIndices.map fun i =>
    let fresh : Policy.Choice := ⟨2 * size + i, 2 * size + i, false, []⟩
    if i = 0 then [⟨0, 0, true, []⟩]
    else match fixture.nodes[i]!.occupant with
      | some k =>
        if protected_.contains k || k = 0 then [fresh] else [⟨k, k, true, []⟩, fresh]
      | none => [fresh]
  let some plan := Policy.select domains
    | throw s!"{fixture.name}: no feasible assignment"
  let nextRef (j : Nat) : Nat :=
    match pinnedOf fixture.nodes[j]! with
    | some k => k
    | none => size + j
  let records := capturedIndices.map fun i =>
    match fixture.nodes[i]!.shared with
    | some k => (size + i, fixtureNode fixture.before[k]! [])
    | none =>
      (size + i, fixtureNode (fixture.nodes[i]!.value.getD 0)
        ((fixture.nodes[i]!.children.getD #[]).toList.map nextRef))
  let image (id : Nat) : Nat := if id < size then id else identityOf plan (id - size)
  let result := publishRecords image (fun _ => id) records before
  let mut identities := #[]
  let mut values := #[]
  let mut edges := #[]
  for j in List.range count do
    let identity := identityOf plan j
    identities := identities.push identity
    match result.lookup identity with
    | some (.plainObject _ (⟨_, .atom value⟩ :: rest)) =>
      values := values.push value
      let mut children := #[]
      for ⟨_, child⟩ in rest do
        match child with
        | .ref r => children := children.push r
        | _ => throw s!"{fixture.name}: unexpected atom child"
      edges := edges.push children
    | _ => throw s!"{fixture.name}: missing output payload"
  return { name := fixture.name, identities, values, edges }

def run (args : List String) : IO UInt32 := do
  let path := args.headD "lean/fixtures/pruned-fixtures.json"
  let content ← IO.FS.readFile path
  let parsed := Json.parse content >>= fromJson? (α := Array Fixture)
  match parsed >>= (·.mapM runFixture) with
  | .error error => IO.eprintln error; return 1
  | .ok observations => IO.println (toJson observations).compress; return 0

end Reconcile.PrunedOracle
