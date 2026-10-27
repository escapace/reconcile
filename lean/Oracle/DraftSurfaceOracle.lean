import Produce.DraftSurface
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `DraftSurface` family: the admission of every draft kind and key class, and
whether `produce` keeps an object or array with one or two getters, changed or not, under
`DraftSurface`.
-/

namespace Reconcile.DraftSurfaceOracle

open Reconcile.DraftSurface Reconcile.Enumerate Reconcile.Protocol Lean

private def kinds : List Kind := [.object, .array, .collection, .typed, .native]
private def keys : List Key := [.index, .length, .other]
private def returns : List Returned := [.primitive, .keptChild, .changedChild, .handle]

private structure Admission where
  kind : Nat
  key : Nat
  admits : Bool
  deriving ToJson

private structure Keeping where
  kind : Nat
  dataChanged : Bool
  returned : List Nat
  keeps : Bool
  deriving ToJson

/-- Every kind and key class with its admission, then every object and array with one or two
getters, changed or not, with whether `produce` keeps it. Indices follow the lists above. -/
def run : IO Unit :=
  emitCorpus ((kinds.flatMap fun kind => keys.map fun key => Sum.inl (kind, key)) ++
    ((kinds.filter holdsGetters).flatMap fun kind => [false, true].flatMap fun dataChanged =>
      (wordsUpTo 2 returns).tail.map fun returned => Sum.inr (kind, dataChanged, returned)))
    fun
    | .inl (kind, key) => toJson
      ({ kind := kinds.idxOf kind, key := keys.idxOf key, admits := admits kind key } : Admission)
    | .inr (kind, dataChanged, returned) => toJson
      ({ kind := kinds.idxOf kind, dataChanged, returned := returned.map returns.idxOf,
         keeps := keeps dataChanged returned } : Keeping)

end Reconcile.DraftSurfaceOracle
