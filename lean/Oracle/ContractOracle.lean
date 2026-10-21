import Produce.Immutable
import Lean

/-! Oracle for the `Contract` family. It runs each graph in `reuse-fixtures.json` through
`Policy.select` and the verified immutable core (`Immutable.publish`), checks the compiler facts,
the readback and the unchanged input frame, and reports the selected identities, values and edges.
-/

namespace Reconcile.ContractOracle

open Lean

structure ReuseFixture where
  name : String
  before : Array Nat
  after : Array Nat
  children : Array (Array Nat)
  undo : Bool
  wrappedOf : Option (Array (Option Nat))
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

private def runFixture (fixture : ReuseFixture) : Except String ReuseObservation := do
  let size := fixture.before.size
  if size = 0 || fixture.after.size != size || fixture.children.size != size then
    throw s!"{fixture.name}: mismatched fixture sizes"
  if fixture.children.any (·.any (· >= size)) then
    throw s!"{fixture.name}: dangling reference"
  let ids := List.range size
  let records := ids.map fun i => (i, fixtureNode fixture.after[i]! fixture.children[i]!)
  let before := publishRecords id (fun _ => id)
    (ids.map fun i => (i, fixtureNode fixture.before[i]! fixture.children[i]!)) ∅
  let wrappedOf := fixture.wrappedOf.getD #[]
  if wrappedOf.any (fun value => value.any (· >= size)) then
    throw s!"{fixture.name}: dangling storage reference"
  let storage := fun r => ((wrappedOf[r]?).join).getD r
  let domains : Policy.Domains := ids.map fun i =>
    let fresh : Policy.Choice := ⟨i + size, i + size, false, []⟩
    if fixture.before[i]! = fixture.after[i]! then
      [⟨i, storage i, true,
        fixture.children[i]!.toList.map fun child => ⟨child, child⟩⟩, fresh]
    else [fresh]
  let some plan := Policy.select domains
    | throw s!"{fixture.name}: no feasible assignment"
  if hzero : plan.length = 0 then
    throw s!"{fixture.name}: empty assignment"
  else
    if plan.length != size then
      throw s!"{fixture.name}: incomplete assignment"
    let finite := fun n => (⟨n % plan.length, Nat.mod_lt _ (Nat.pos_of_ne_zero hzero)⟩ : Fin plan.length)
    let finiteRecords := (List.finRange plan.length).map fun i =>
      (i, (fixtureNode fixture.after[i.val]! fixture.children[i.val]!).remap finite id)
    let input : Immutable.Input Nat plan := {
      source := publishRecords id (fun _ => id) finiteRecords ∅
      before := before
      proposed := Fin.val
      fresh := fun i => i.val + size
      storage := storage
      proto := fun _ => id
      records := finiteRecords
    }
    if !Immutable.checkCompiled input domains then
      throw s!"{fixture.name}: invalid compiler facts"
    let result := Immutable.publish input
    let image := fun i => Immutable.image plan (finite i)
    if !checkPublication image (fun _ => id) records result then
      throw s!"{fixture.name}: immutable core failed readback"
    if ids.any (fun r => result.lookup r != before.lookup r) then
      throw s!"{fixture.name}: input frame changed"
    let mut values := #[]
    let mut edges := #[]
    for i in ids do
      match result.lookup (image i) with
      | some (.plainObject _ (⟨_, .atom value⟩ :: rest)) =>
        values := values.push value
        let mut children := #[]
        for ⟨_, child⟩ in rest do
          match child with
          | .ref r => children := children.push r
          | _ => throw "unexpected atom child"
        edges := edges.push children
      | _ => throw "missing output payload"
    return { name := fixture.name, identities := (ids.map image).toArray, values, edges }

def run (args : List String) : IO UInt32 := do
  let path := args.headD "lean/fixtures/reuse-fixtures.json"
  let content ← IO.FS.readFile path
  let parsed := Json.parse content >>= fromJson? (α := Array ReuseFixture)
  match parsed >>= (·.mapM runFixture) with
  | .error error => IO.eprintln error; return 1
  | .ok observations => IO.println (toJson observations).compress; return 0

end Reconcile.ContractOracle
