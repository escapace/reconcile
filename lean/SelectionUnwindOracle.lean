import SelectionUnwind
import Mathlib.Data.Finset.Sort

/-! Selected-prefix backtracking restoration.
Retained because individual undo and their composition describe the current selector's
demand trail, owner set, forced followers and score. The bridge executes reference
transitions with native incoming-demand updates, not a production bulk tier exit.
The reverted retention-capacity tier exit is not modeled; no retained-capacity producer is imported. -/

namespace Reconcile.SelectionUnwindOracle

open Policy SelectionUnwind IncomingConsensus Lean

structure InputFrame where
  node : Nat
  choice : Choice
  followers : List Nat
  deriving FromJson

structure Input where
  forceOwners : List Nat
  frames : List InputFrame
  keep : Nat
  deriving FromJson

structure Observation where
  demands : List (List Nat)
  trail : List (Nat × List Nat)
  owners : List Nat
  forced : List Nat
  retained : Nat
  deriving ToJson, DecidableEq

def summary : Summary Nat → List Nat
  | .empty => []
  | .one id => [id]
  | .conflict => [0, 0]

def observe (width : Nat) (state : State) : Observation where
  demands := (List.range width).map fun node => summary (state.demands.1 node)
  trail := state.demands.2.map fun (node, old) => (node, summary old)
  owners := state.owners.sort (· ≤ ·)
  forced := state.forced.sort (· ≤ ·)
  retained := state.retained

def check (input : Input) : IO (List Observation × List Observation) := do
  let problem : ForcedGroups.Problem := {
    nodes := ∅
    literals := ∅
    owner := fun id => input.forceOwners[id]?.getD id
    choice := fun _ => ⟨0, 0, false, []⟩ }
  let frames := input.frames.map fun frame =>
    ({ node := frame.node, choice := frame.choice, followers := frame.followers.toFinset } : Frame)
  if input.keep > frames.length then throw (IO.userError "Invalid retained prefix length")
  let width := 1 + (frames.flatMap fun frame =>
    frame.node :: frame.choice.required.map Requirement.node).foldl max 0
  let mut state := empty
  let mut assignments := [observe width state]
  for frame in frames do
    if !decide ((frame.followers.sort (· ≤ ·)).map problem.owner).Nodup then
      throw (IO.userError "Duplicate forced position")
    if !decide (Available problem state frame) then
      throw (IO.userError "Invalid unwind admission")
    state := assign state frame
    assignments := observe width state :: assignments
  let mut undos := [observe width state]
  for frame in (frames.drop input.keep).reverse do
    state := unassign problem state frame
    undos := observe width state :: undos
  let expected := (frames.take input.keep).foldl assign empty
  if observe width state != observe width expected then
    throw (IO.userError "Prefix restoration disagreement")
  pure (assignments.reverse, undos.reverse)

def run (raw : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse raw)
  let inputs : Array Input ← IO.ofExcept (fromJson? json)
  let results ← inputs.mapM check
  (← IO.getStdout).putStrLn (toJson results).compress

end Reconcile.SelectionUnwindOracle
