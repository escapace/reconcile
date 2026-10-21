import Types.OwnedNativeChild
import Lean

/-! Oracle for the `OwnedNativeChild` family: adoption of a captured URL carrier and its
parameter child under `Types.OwnedNativeChild`, reporting the query, entries, owner and child
identities, admission, construction response and reuse. -/

namespace Reconcile.OwnedNativeChildOracle
open Lean OwnedNativeChild

structure Input where
  captured : List (String × String)
  source : List (String × String)
  sourceQuery : String
  canonicalQuery : String
  touched : Bool
  owner : Nat
  child : Nat
  actualChild : Nat
  metadata : Option Nat := none
  equal : Bool := true
  forced : Bool := false
  ownerChanged : Bool := false
  deriving FromJson

def evaluate (input : Input) : Json :=
  let serialize := fun entries => (input.canonicalQuery, entries)
  let state : State (List (String × String)) (String × List (String × String)) :=
    ⟨input.owner, input.child, input.captured, ("", input.captured), input.touched, false⟩
  let adopted := adopt serialize Prod.snd (input.sourceQuery, input.source) state
  Json.mkObj [
    ("query", toJson adopted.query.1),
    ("entries", toJson adopted.payload),
    ("child", toJson adopted.child),
    ("owner", toJson adopted.carrier),
    ("admitted", toJson (admit (fun _ => input.actualChild) input.owner input.child)),
    ("response", toJson (constructionResponse (fun _ => input.metadata) input.child)),
    ("reuse", toJson (chooseReuse input.equal (forceChild input.forced input.ownerChanged)))]

def run (input : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse input)
  let inputs ← IO.ofExcept (fromJson? (α := Array Input) json)
  (← IO.getStdout).putStrLn (toJson (inputs.map evaluate)).compress

end Reconcile.OwnedNativeChildOracle
