import Serialization.Collection
import Lean

namespace Reconcile.SerializationCollectionOracle
open Lean SerializationCollection

structure Request where
  map : Bool
  values : List Nat
  failAt : Option Nat
  deriving FromJson

-- Bridge codes 5 and 6 represent -0 and +0; native keys canonicalize both to +0.
-- Other codes are distinct resolved atoms or stable allocated object identities.
def canonical (key : Nat) : Nat := if key = 5 then 6 else key

def evaluate (request : Request) : Json := Id.run do
  let read := fun token => if request.failAt = some token then Except.error token
    else Except.ok (request.values[token]?.getD 0)
  let tokens := List.range request.values.length
  if request.map then
    let pairs := (List.range (request.values.length / 2)).map fun i => (i * 2, i * 2 + 1)
    let result := resolvedMap canonical read [] pairs
    return Json.mkObj [("entries", toJson result.rows), ("reads", toJson result.trace.reads),
      ("error", toJson result.trace.error)]
  else
    let result := resolvedSet canonical read [] tokens
    return Json.mkObj [("entries", toJson result.keys), ("reads", toJson result.trace.reads),
      ("error", toJson result.trace.error)]

def run (input : String) : IO Unit := do
  let requests ← IO.ofExcept (Json.parse input >>= fromJson? (α := List Request))
  (← IO.getStdout).putStrLn (toJson (requests.map evaluate)).compress

end Reconcile.SerializationCollectionOracle
