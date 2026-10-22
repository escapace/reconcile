import Property.WriteFreeReadback
import Lean

/-! Oracle for the `WriteFreeReadback` family: `reconcile` of a plain object onto `{a: 1, b: 2}`
from every ordered subset of the keys `a`, `b` and `c`, each holding its wanted value or another,
and of an array onto `[1, 2]` and `[1, hole]` from every array of length up to three whose
elements are the wanted value, another value or a hole. Each row reports whether publication
writes nothing (`objectWriteFree`, `arrayWriteFree`) and whether the readback accepts what it
observes before any write. -/

namespace Reconcile.WriteFreeReadbackOracle

open Reconcile.PropertyWrite Reconcile.WriteFreeReadback Lean

/-- Keys 0, 1 and 2 are `a`, `b` and `c`; `a` and `b` are requested with 1 and 2. -/
def wantObject (k : Nat) : Nat := k + 1

/-- Every ordered list of distinct keys from `a`, `b` and `c`. -/
def orders : List (List Nat) :=
  [[], [0], [1], [2], [0, 1], [1, 0], [0, 2], [2, 0], [1, 2], [2, 1],
    [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

/-- Each listed key holds its wanted value (`true`) or 9; `c` always holds 9. -/
def assignments : List Nat → List (List Bool)
  | [] => [[]]
  | k :: rest =>
    let tails := assignments rest
    (if k = 2 then [false] else [true, false]).flatMap fun b => tails.map (b :: ·)

def valueOf (k : Nat) (same : Bool) : Nat := if same then wantObject k else 9

def objectObserved (keys : List Nat) (same : List Bool) : Observed Nat Nat where
  keys := keys
  slot k := match (keys.zip same).lookup k with
    | some b => ⟨some (.data (valueOf k b) plain), .none, true⟩
    | none => ⟨none, .none, true⟩

private structure ObjectRow where
  keys : List Nat
  values : List Nat
  writeFree : Bool
  accepts : Bool
  deriving ToJson

/-- Requested arrays: `[1, 2]` and `[1, hole]`. -/
def wanted : List (List (Option Nat)) := [[some 1, some 2], [some 1, none]]

/-- An element of an observed array: the wanted value, 9 or a hole. -/
def elementChoices (want : Option Nat) : List (Option Nat) :=
  [want, some 9, none].eraseDups

def arrays : Nat → List (Option Nat) → List (List (Option Nat))
  | 0, _ => [[]]
  | n + 1, want =>
    (elementChoices (want.headD none)).flatMap fun e => (arrays n want.tail).map (e :: ·)

private structure ArrayRow where
  wanted : Nat
  elements : List (Option Nat)
  writeFree : Bool
  accepts : Bool
  deriving ToJson

def arrayAccepts (want : List (Option Nat)) (o : List (Option Nat)) : Bool :=
  decide (o.length = want.length) &&
    (List.range want.length).all fun i => decide (o.getD i none = want.getD i none)

def run : IO Unit := do
  let objects := orders.flatMap fun keys => (assignments keys).map (keys, ·)
  let arrayCases := (List.range wanted.length).flatMap fun w =>
    (List.range 4).flatMap fun n => (arrays n (wanted.getD w [])).map (w, ·)
  IO.println (objects.length + arrayCases.length)
  for (keys, same) in objects do
    let o := objectObserved keys same
    IO.println (toJson ({
      keys, values := (keys.zip same).map fun (k, b) => valueOf k b
      writeFree := objectWriteFree [0, 1] wantObject o
      accepts := decide (o.keys = [0, 1]) && [0, 1].all fun k => readsAs (o.slot k) (wantObject k)
      } : ObjectRow)).compress
  for (w, elements) in arrayCases do
    let want := wanted.getD w []
    let o : ObservedArray Nat := ⟨elements.length, fun i => elements.getD i none⟩
    IO.println (toJson ({
      wanted := w, elements
      writeFree := arrayWriteFree want.length (fun i => want.getD i none) o
      accepts := arrayAccepts want elements } : ArrayRow)).compress

end Reconcile.WriteFreeReadbackOracle
