import Spec.Reconcile
import Spec.Produce
import Oracle.Protocol

/-! Oracle for the `Spec` family: runs the executable reference models over graphs the random
differential bridge generates. Each request names the operation and carries the graphs. A
`reconcile` outcome reports a call rejected because its decision would change `next` with
`changesNext` set (`Spec.KeepsNext`), apart from every other rejection. -/

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
candidates in decision order, with the requirements each one's fixed slots make; the decision
of each pass, up to the first that keeps no root or would change `next`, where the call stops;
and whether the call stops because the last decision would change `next`, as `run` reports it
(`phases_changesNext`). -/
structure Phases where
  order : List Nat
  first : Array (Option Nat)
  pinned : Array Bool
  candidates : Array (List Nat)
  required : Array (List (List (Nat × Nat)))
  rounds : List (Array (Option Nat))
  changesNext : Bool
  deriving ToJson

open Reconcile in
/-- The passes of `run` on a normalized input, and whether the last one keeps the root but would
change `next`. -/
def roundsOf (input : Input) (al : Discovery) : List (Array (Option Nat)) × Bool :=
  match input.cur.root, input.next.root with
  | .ref _, .ref r =>
    let passes := rounds input al r
    let final := passes.getLastD #[]
    (passes, (final[r]?.bind id).isSome && !keepsNext input final)
  | _, _ => ([], false)

open Reconcile in
/-- The phases of `Reconcile.run` on `raw`. A current object inside a pinned subtree, which no
decision can keep elsewhere, is no candidate, as the runtime's discovery has it. -/
def phases (raw : Reconcile.Input) : Phases :=
  let input := normalized raw
  let al := discover input
  let pin := al.pinned
  let n := input.next.nodes.size
  let held := (List.range n).filterMap (pinnedObject input pin)
  let candidatesAt (j : Nat) : List Nat :=
    (passCandidates input al [] j).filter fun x => admitted input pin j x && !held.contains x
  { order := al.order, first := al.first, pinned := pin,
    candidates := (Array.range n).map candidatesAt,
    required := (Array.range n).map fun j => (candidatesAt j).map (fixedRequirements input j),
    rounds := (roundsOf input al).1,
    changesNext := (roundsOf input al).2 }

open Reconcile in
/-- The phases report the rejection `run` reports. -/
theorem phases_changesNext (raw : Reconcile.Input) :
    (phases raw).changesNext = (Reconcile.run raw).changesNext := by
  simp only [phases, roundsOf, Reconcile.run]
  generalize normalized raw = input
  split
  · next c r hc hn =>
    simp only [hc, hn]
    generalize rounds input (discover input) r = passes
    generalize passes.getLastD #[] = final
    cases h : final[r]?.bind id with
    | none => simp
    | some x => cases k : keepsNext input final <;> simp [publish]
  · next hne =>
    split
    · next c r hc hn => exact (hne c r hc hn).elim
    · rfl

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

def run (input : String) : IO Unit := Protocol.serveArray input answer

end Reconcile.SpecOracle
