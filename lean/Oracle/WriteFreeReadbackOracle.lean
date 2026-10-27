import Property.WriteFreeReadback
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `WriteFreeReadback` family: `reconcile` of a plain object onto `{a: 1, b: 2}`
from every ordered subset of the keys `a`, `b` and `c`, each holding its wanted value or another,
and of an array onto `[1, 2]` and `[1, hole]` from every array of length up to three whose
elements are the wanted value, another value or a hole. Each row reports whether publication
writes nothing (`objectWriteFree`, `arrayWriteFree`) and whether the readback accepts what it
observes before any write (`objectMatches`, `arrayMatches`). -/

namespace Reconcile.WriteFreeReadbackOracle

open Reconcile.PropertyWrite Reconcile.WriteFreeReadback Reconcile.Enumerate Reconcile.Protocol
  Lean

/-- Keys 0, 1 and 2 are `a`, `b` and `c`; `a` and `b` are requested with 1 and 2. -/
def wantObject (k : Nat) : Nat := k + 1

/-- Every ordered list of distinct keys from `a`, `b` and `c`. -/
def orders : List (List Nat) := arrangements [0, 1, 2]

/-- Each listed key holds its wanted value (`true`) or 9; `c` always holds 9. -/
def assignments (keys : List Nat) : List (List Bool) :=
  product (keys.map fun k => if k = 2 then [false] else [true, false])

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

/-- Every array of `length` elements that can be observed for `want`. -/
def arrays (length : Nat) (want : List (Option Nat)) : List (List (Option Nat)) :=
  product ((List.range length).map fun i => elementChoices (want.getD i none))

private structure ArrayRow where
  wanted : Nat
  elements : List (Option Nat)
  writeFree : Bool
  accepts : Bool
  deriving ToJson

def run : IO Unit :=
  emitCorpus ((orders.flatMap fun keys =>
      (assignments keys).map fun same => Sum.inl (keys, same)) ++
    ((List.range wanted.length).flatMap fun w => (List.range 4).flatMap fun n =>
      (arrays n (wanted.getD w [])).map fun elements => Sum.inr (w, elements)))
    fun
    | .inl (keys, same) =>
      let o := objectObserved keys same
      toJson ({
        keys, values := (keys.zip same).map fun (k, b) => valueOf k b
        writeFree := objectWriteFree [0, 1] wantObject o
        accepts := decide (objectMatches [0, 1] wantObject o) } : ObjectRow)
    | .inr (w, elements) =>
      let want := wanted.getD w []
      let wantAt := fun i => want.getD i none
      let o : ObservedArray Nat := ⟨elements.length, fun i => elements.getD i none⟩
      toJson ({
        wanted := w, elements
        writeFree := arrayWriteFree want.length wantAt o
        accepts := decide (arrayMatches want.length wantAt o) } : ArrayRow)

end Reconcile.WriteFreeReadbackOracle
