import Produce.SettledChildren
import Lean

/-! Oracle for the `SettledChildren` family: every graph of three objects whose child lists hold
at most two entries, with no object changed or one changed, asked whether object 0 and then
object 1 need a copy, with `Produce.SettledChildren.needs`. Each row reports both answers and,
after each, the settled answers and the kept child lists. -/

namespace Reconcile.SettledChildrenOracle

open Reconcile.SettledChildren Lean

/-- Child lists of at most two entries over three objects, in a fixed order. -/
def lists : List (List Nat) :=
  [[]] ++ (List.range 3).map (fun a => [a]) ++
    (List.range 3).flatMap (fun a => (List.range 3).map (fun b => [a, b]))

private structure Answer where
  needs : Bool
  memo : List (Option Bool)
  recorded : List (Option (List Nat))
  deriving ToJson

private structure Observation where
  children : List (List Nat)
  changed : Int
  answers : List Answer
  deriving ToJson

private def answer (r : Bool × State) : Answer :=
  { needs := r.1, memo := (List.range 3).map r.2.memo,
    recorded := (List.range 3).map r.2.recorded }

def run : IO Unit := do
  let graphs := lists.flatMap fun a => lists.flatMap fun b => lists.map fun c => [a, b, c]
  let cases := graphs.flatMap fun children => [-1, 0, 1, 2].map ((children, ·) : Int → _)
  IO.println cases.length
  for (children, changed) in cases do
    let g : Graph := fun n => children.getD n []
    let o : Oracle :=
      { fact := fun _ _ => false, changed := fun _ n => (n : Int) == changed,
        after := fun _ _ => false }
    let first := needs g o 8 initial 0
    let second := needs g o 8 first.2 1
    IO.println (toJson ({ children, changed, answers := [answer first, answer second] } :
      Observation)).compress

end Reconcile.SettledChildrenOracle
