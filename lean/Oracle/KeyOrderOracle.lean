import Property.KeyOrder
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `KeyOrder` family: the own keys `KeyOrder` gives for every creation order of up
to five keys followed by up to two assignments or deletions. -/

namespace Reconcile.KeyOrderOracle

open Reconcile.PropertyOrder Reconcile.KeyOrder Reconcile.Enumerate Reconcile.Protocol Lean

private def alphabet : List Key := [.index 0, .index 1, .name 0, .name 1, .symbol 0]

private def operations : List Op := alphabet.flatMap fun key => [.assign key, .remove key]

/-- An assignment as `2 * code`, a deletion as `2 * code + 1`. -/
private def encodeOp : Op → Nat
  | .assign key => 2 * keyCode key
  | .remove key => 2 * keyCode key + 1

private structure Observation where
  created : List Nat
  ops : List Nat
  own : List Nat
  deriving ToJson

/-- Every creation order of up to five keys and every sequence of up to two assignments or
deletions, with the own keys the model gives (`produce_key_order` relates `produce` to them). -/
def run : IO Unit :=
  emitCorpus ((arrangements alphabet).flatMap fun created =>
      (wordsUpTo 2 operations).map (created, ·))
    fun (created, ops) =>
      ({ created := created.map keyCode, ops := ops.map encodeOp
         own := (ownKeys (KeyOrder.run created ops)).map keyCode } : Observation)

end Reconcile.KeyOrderOracle
