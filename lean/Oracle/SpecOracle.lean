import Spec.Reconcile
import Spec.Produce
import Lean

/-! Oracle for the `Spec` family: runs the executable reference models over graphs the random
differential bridge generates. Each request names the operation and carries the graphs. -/

namespace Reconcile.SpecOracle

open Lean Spec

structure Request where
  op : String
  cur : Graph
  next : Graph := default
  same : Array (Option Nat) := #[]
  ops : Array Produce.Op := #[]
  returns : Val := .prim .undef
  returnsCurrent : Bool := false

/-- A field an operation does not use may be absent. -/
def field (j : Json) (name : String) (default : α) [FromJson α] : Except String α :=
  match j.getObjVal? name with
  | .ok v => fromJson? v
  | .error _ => pure default

instance : FromJson Request where
  fromJson? j := do
    let op ← (← j.getObjVal? "op").getStr?
    let cur : Graph ← fromJson? (← j.getObjVal? "cur")
    let next : Graph ← field j "next" default
    let same : Array (Option Nat) ← field j "same" #[]
    let ops : Array Produce.Op ← field j "ops" #[]
    let returns : Val ← field j "returns" (.prim .undef)
    let returnsCurrent : Bool ← field j "returnsCurrent" false
    pure { op, cur, next, same, ops, returns, returnsCurrent }

def answer (request : Request) : Except String Json :=
  match request.op with
  | "reconcile" =>
    pure (toJson (Reconcile.run ⟨request.cur, request.next, request.same⟩))
  | "produce" =>
    pure (toJson (Produce.run
      ⟨request.cur, request.ops.toList, request.returns, request.returnsCurrent⟩))
  | "snapshot" => pure (toJson (Produce.snapshot request.cur))
  | op => throw s!"unknown spec operation: {op}"

def run (raw : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse raw)
  let requests : Array Request ← IO.ofExcept (fromJson? json)
  let results ← IO.ofExcept (requests.mapM answer)
  (← IO.getStdout).putStrLn (Json.arr results).compress

end Reconcile.SpecOracle
