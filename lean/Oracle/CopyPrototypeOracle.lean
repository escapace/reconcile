import Types.CopyPrototype
import Lean

/-! Oracle for the `CopyPrototype` family: for every kind, as its own instance and as a subclass
instance, whether a copy keeps the source's prototype (`CopyPrototype.adopt`) and whether
`serialize` accepts it. -/

namespace Reconcile.CopyPrototypeOracle

open Reconcile.CopyPrototype Lean

private structure Observation where
  kind : Nat
  subclass : Bool
  keeps : Bool
  serializes : Bool
  deriving ToJson

/-- Every kind, as its own instance and as a subclass instance, with whether a copy keeps the
source's prototype and whether `serialize` accepts it. -/
def run : IO Unit := do
  IO.println (2 * kinds.length)
  for kind in kinds do
    for subclass in [false, true] do
      let source := if subclass then Proto.subclass kind else Proto.standard kind
      let row : Observation :=
        { kind := kinds.idxOf kind, subclass, keeps := adopt (Proto.standard kind) source == source,
          serializes := serializes source }
      IO.println (toJson row).compress

end Reconcile.CopyPrototypeOracle
