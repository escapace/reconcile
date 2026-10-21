import Property.DeferredOrder
import Property.PropertyOrder
import Lean

/-! Oracle for the `DeferredOrder` family: runs `PropertyOrder`'s reference cursor both eagerly
and deferred to native demands (`DeferredOrder.eager`, `DeferredOrder.deferred`), checks that the
two agree, and reports what each demanded checkpoint observes. -/

open Lean Reconcile.PropertyOrder Reconcile.DeferredOrder

namespace Reconcile.DeferredOrderOracle

structure Input where
  previous : Array (Array Nat)
  desired : Array (Array Nat)
  ordered : Bool
  demands : Array Nat
  finals : Array Bool
  deriving FromJson

def decode (fields : Array Nat) : Except String Key := do
  if fields.size != 2 then throw "Expected key class and label"
  match fields[0]! with
  | 0 => pure (.index fields[1]!)
  | 1 => pure (.name fields[1]!)
  | 2 => pure (.symbol fields[1]!)
  | _ => throw "Invalid key class"

def initial (desired : List Key) : Cursor :=
  { names := desired
    symbols := desired.dropWhile (fun key => match key with | .symbol _ => false | _ => true)
    retained := 0 }

def advance (desired : List Key) (state : Option (Cursor × Bool)) (key : Key) :
    Option (Cursor × Bool) := state.map fun pair =>
  let next := referenceStep desired key pair.1
  (next.cursor, next.kept)

def observe (finalCheck : Bool) : Option (Cursor × Bool) → Json
  | none => Json.null
  | some (cursor, kept) => Json.arr #[toJson cursor.retained,
      if finalCheck then Json.null else toJson kept]

def check (input : Input) : IO Json := do
  let previous ← IO.ofExcept (input.previous.toList.mapM decode)
  let desired ← IO.ofExcept (input.desired.toList.mapM decode)
  let mut commands : List (Command Key) := []
  let mut position := 0
  if input.demands.size != input.finals.size then throw (IO.userError "Demand flag mismatch")
  for id in [:input.demands.size] do
    let through := input.demands[id]!
    if through < position || through > previous.length then
      throw (IO.userError "Demand outside monotone private prefix")
    commands := commands ++ (previous.drop position |>.take (through - position)).map Command.advance
      ++ [.boundary id]
    position := through
  commands := commands ++ (previous.drop position).map Command.advance
  let aligned := previous.zip desired |>.all (fun pair => pair.1 == pair.2)
  let cursor := if input.ordered && !aligned then some (initial desired, false) else none
  let native : Native (Option (Cursor × Bool)) (List Json) :=
    { probe := fun _ world => (world, .ok true)
      consume := fun id current world => (world ++ [observe input.finals[id]! current], none) }
  let reference := eager (advance desired) native commands cursor []
  let candidate := deferred (advance desired) native commands cursor [] []
  if reference.1 != candidate.1 || reference.2 != candidate.2 then
    throw (IO.userError "Deferred cursor model disagreement")
  pure (Json.arr candidate.1.toArray)

end Reconcile.DeferredOrderOracle

def Reconcile.DeferredOrderOracle.run (raw : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse raw)
  let inputs : Array Reconcile.DeferredOrderOracle.Input ← IO.ofExcept (fromJson? json)
  let results ← inputs.mapM Reconcile.DeferredOrderOracle.check
  (← IO.getStdout).putStrLn (Json.arr results).compress
