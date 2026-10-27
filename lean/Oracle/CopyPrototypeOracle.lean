import Types.CopyPrototype
import Oracle.Protocol

/-! Oracle for the `CopyPrototype` family: for every kind, as its own instance, as a subclass
instance and, for a typed array, given another typed kind's standard prototype, whether a copy
keeps the source's prototype (`CopyPrototype.adopt`) and whether `serialize` accepts it. -/

namespace Reconcile.CopyPrototypeOracle

open Reconcile.CopyPrototype Reconcile.Protocol Lean

private structure Observation where
  kind : Nat
  subclass : Bool
  /-- The index of the typed kind whose standard prototype the value was given, if another. -/
  other : Option Nat
  keeps : Bool
  serializes : Bool
  deriving ToJson

private def isTyped : Kind → Bool
  | .typed _ => true
  | _ => false

/-- The typed kinds other than `kind` whose prototype a typed array of `kind` can be given. -/
private def others (kind : Kind) : List Kind :=
  if isTyped kind then kinds.filter fun other => other != kind && isTyped other else []

/-- Every kind, as its own instance, as a subclass instance and given each other typed kind's
standard prototype, with whether a copy keeps the source's prototype and whether `serialize`
accepts it. -/
def run : IO Unit :=
  emitCorpus (kinds.flatMap fun kind =>
    [(kind, Proto.standard kind, false, none), (kind, Proto.subclass kind, true, none)] ++
      (others kind).map fun other => (kind, Proto.standard other, false, some (kinds.idxOf other)))
    fun (kind, source, subclass, other) =>
      ({ kind := kinds.idxOf kind, subclass, other,
         keeps := adopt (Proto.standard kind) source == source,
         serializes := serializes kind source } : Observation)

end Reconcile.CopyPrototypeOracle
