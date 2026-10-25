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
  classes : Array (List (String × Slot)) := #[]
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
    let classes : Array (List (String × Slot)) ← field j "classes" #[]
    let ops : Array Produce.Op ← field j "ops" #[]
    let returns : Val ← field j "returns" (.prim .undef)
    let returnsCurrent : Bool ← field j "returnsCurrent" false
    pure { op, cur, next, same, classes, ops, returns, returnsCurrent }

/-- The phases of the reference for one case, which the runtime's discovery and decisions must
agree with: the visit order, the pinning alignment and the pinned nodes; each node's admitted
candidates in decision order, with the requirements each one's fixed slots make; and the decision
of each pass, up to the first that keeps no root, where the call stops. -/
structure Phases where
  order : List Nat
  first : Array (Option Nat)
  pinned : Array Bool
  candidates : Array (List Nat)
  required : Array (List (List (Nat × Nat)))
  rounds : List (Array (Option Nat))
  deriving ToJson

open Reconcile in
/-- The phases of `Reconcile.run` on `raw`. A current object inside a pinned subtree, which no
decision can keep elsewhere, is no candidate, as the runtime's discovery has it. -/
def phases (raw : Reconcile.Input) : Phases :=
  let input := normalized raw
  let al := discover input
  let pin := al.pinned
  let n := input.next.nodes.size
  let root := input.next.root.refId
  let held := (List.range n).filterMap fun j =>
    if pin[j]?.getD false then input.same[j]?.bind id else none
  let candidatesAt (j : Nat) : List Nat :=
    (if root = some j then input.cur.root.refId.toList else orderedCandidates input al j).filter
      fun x => admitted input pin j x && !held.contains x
  let requiredOf (j x : Nat) : List (Nat × Nat) :=
    (fixedPairs (input.cur.node x) (input.next.node j)).filterMap fun
      | (.ref x', .ref c') => some (c', x')
      | _ => none
  let rounds := match input.cur.root, root with
    | .ref _, some r =>
      let initial := decide input al pin [] []
      if (initial[r]?.bind id).isNone then [initial]
      else
        let all := demote input al pin (fuelOf input) [] []
        match all.findIdx? (fun kept => (kept[r]?.bind id).isNone) with
        | some i => all.take (i + 1)
        | none => all
    | _, _ => []
  { order := al.order, first := al.first, pinned := pin,
    candidates := (Array.range n).map candidatesAt,
    required := (Array.range n).map fun j => (candidatesAt j).map (requiredOf j), rounds }

def answer (request : Request) : Except String Json :=
  match request.op with
  | "reconcile" =>
    pure (toJson (Reconcile.run ⟨request.cur, request.next, request.same, request.classes⟩))
  | "reconcile-phases" =>
    pure (toJson (phases ⟨request.cur, request.next, request.same, request.classes⟩))
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
