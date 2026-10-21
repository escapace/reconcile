import Produce.DraftSurface
import Lean

/-! Oracle for the `DraftSurface` family: the admission of every draft kind and key class, and
whether `produce` keeps an object with one or two getters, changed or not, under `DraftSurface`.
-/

namespace Reconcile.DraftSurfaceOracle

open Reconcile.DraftSurface Lean

private def kinds : List Kind := [.object, .array, .collection, .typed, .native]
private def keys : List Key := [.index, .length, .other]
private def returns : List Returned := [.primitive, .keptChild, .changedChild, .handle]

private structure Admission where
  kind : Nat
  key : Nat
  admits : Bool
  deriving ToJson

private structure Keeping where
  dataChanged : Bool
  returned : List Nat
  keeps : Bool
  deriving ToJson

/-- Every kind and key class with its admission, then every object with one or two getters,
changed or not, with whether `produce` keeps it. Indices follow the lists above. -/
def run : IO Unit := do
  let lists := returns.map ([·]) ++ returns.flatMap fun a => returns.map fun b => [a, b]
  IO.println (kinds.length * keys.length + 2 * lists.length)
  for kind in kinds do
    for key in keys do
      let row : Admission :=
        { kind := kinds.idxOf kind, key := keys.idxOf key, admits := admits kind key }
      IO.println (toJson row).compress
  for dataChanged in [false, true] do
    for returned in lists do
      let row : Keeping :=
        { dataChanged, returned := returned.map returns.idxOf, keeps := keeps dataChanged returned }
      IO.println (toJson row).compress

end Reconcile.DraftSurfaceOracle
