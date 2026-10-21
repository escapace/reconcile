import Property.KeyOrder
import Lean

/-! Oracle for the `KeyOrder` family: the own keys `KeyOrder` gives for every creation order of up
to five keys followed by up to two assignments or deletions. -/

namespace Reconcile.KeyOrderOracle

open Reconcile.PropertyOrder Reconcile.KeyOrder Lean

private def arrangements : List Key → List (List Key)
  | [] => [[]]
  | keys => [] :: keys.flatMap fun key =>
      (arrangements (keys.erase key)).map (key :: ·)
termination_by keys => keys.length
decreasing_by
  rename_i h
  exact List.length_erase_of_mem h ▸ Nat.sub_lt (List.length_pos_of_mem h) Nat.one_pos

private def alphabet : List Key := [.index 0, .index 1, .name 0, .name 1, .symbol 0]

private def operations : List Op := alphabet.flatMap fun key => [.assign key, .remove key]

private def encode : Key → Nat
  | .index label => 3 * label
  | .name label => 3 * label + 1
  | .symbol label => 3 * label + 2

/-- An assignment as `2 * code`, a deletion as `2 * code + 1`. -/
private def encodeOp : Op → Nat
  | .assign key => 2 * encode key
  | .remove key => 2 * encode key + 1

private structure Observation where
  created : List Nat
  ops : List Nat
  own : List Nat
  deriving ToJson

/-- Every creation order of up to five keys and every sequence of up to two assignments or
deletions, with the own keys the model gives (`produce_key_order` relates `produce` to them). -/
def run : IO Unit := do
  let sequences : List (List Op) :=
    [] :: operations.map ([·]) ++ operations.flatMap fun a => operations.map fun b => [a, b]
  let created := arrangements alphabet
  IO.println (created.length * sequences.length)
  for base in created do
    for ops in sequences do
      let observation : Observation :=
        { created := base.map encode, ops := ops.map encodeOp
          own := (ownKeys (KeyOrder.run base ops)).map encode }
      IO.println (toJson observation).compress

end Reconcile.KeyOrderOracle
