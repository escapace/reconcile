import Property.DeferredOrder
import Property.PropertyOrder
import Oracle.Protocol

/-! Oracle for the `DeferredOrder` family: runs `PropertyOrder`'s reference cursor deferred to
native demands (`DeferredOrder.deferred`), which `execute_eq` equates with running it eagerly,
and reports what each demanded checkpoint observes. -/

namespace Reconcile.DeferredOrderOracle

open Lean Reconcile.PropertyOrder Reconcile.DeferredOrder Reconcile.Protocol

/-- One preflight's trace: the current and desired keys as `keyCode`s, and for each demand the
length of the private prefix it needs and whether it is the final one. -/
structure Input where
  previous : Array Nat
  desired : Array Nat
  ordered : Bool
  demands : Array Nat
  finals : Array Bool
  deriving FromJson

def advance (desired : List Key) (state : Option (Cursor × Bool)) (key : Key) :
    Option (Cursor × Bool) := state.map fun pair =>
  let next := referenceStep desired key pair.1
  (next.cursor, next.kept)

def observe (finalCheck : Bool) : Option (Cursor × Bool) → Json
  | none => Json.null
  | some (cursor, kept) => Json.arr #[toJson cursor.retained,
      if finalCheck then Json.null else toJson kept]

/-- Checks that the demands are paired with their flags and read a growing prefix of the current
keys. -/
def check (input : Input) : Except String Json := do
  let previous := input.previous.toList.map keyOfCode
  let desired := input.desired.toList.map keyOfCode
  let mut commands : List (Command Key) := []
  let mut position := 0
  if input.demands.size != input.finals.size then throw "Demand flag mismatch"
  for id in [:input.demands.size] do
    let through := input.demands[id]!
    if through < position || through > previous.length then
      throw "Demand outside monotone private prefix"
    commands := commands ++ (previous.drop position |>.take (through - position)).map Command.advance
      ++ [.boundary id]
    position := through
  commands := commands ++ (previous.drop position).map Command.advance
  let aligned := previous.zip desired |>.all (fun pair => pair.1 == pair.2)
  let cursor :=
    if input.ordered && !aligned then some (PropertyOrder.initial desired, false) else none
  let native : Native (Option (Cursor × Bool)) (List Json) :=
    { probe := fun _ world => (world, .ok true)
      consume := fun id current world => (world ++ [observe input.finals[id]! current], none) }
  pure (Json.arr (deferred (advance desired) native commands cursor [] []).1.toArray)

def run (input : String) : IO Unit := serveArray input check

end Reconcile.DeferredOrderOracle
