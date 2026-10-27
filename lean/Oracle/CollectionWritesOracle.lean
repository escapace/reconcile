import Graph.CollectionPlan
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `CollectionWrites` family: `CollectionPlan.publish` of a kept `Set` or `Map`,
for every pair of current and next entry lists whose keys are drawn from four, distinct within each
list: up to four members for a `Set`, and up to three entries for a `Map`, each holding value 0
or 1. Each row reports the writes, deletes and puts, in order, and the `unchanged` flag. An entry
crosses as its slots: its key, then a `Map` entry's value. Distinct keys, the premise of
`publish_result`, hold by construction; that the writes then leave the next entries is
`publish_result`, so no row repeats them. -/

namespace Reconcile.CollectionWritesOracle

open Reconcile.CollectionPlan Reconcile.Enumerate Reconcile.Protocol Lean

/-- The keys, labelled 0 to 3. -/
def keyLabels : List Nat := List.range 4

/-- Every `Set`'s members: up to four distinct keys, 1 + 4 + 12 + 24 + 24 lists. A member is a
key with no value. -/
def sets : List (List (Nat × Unit)) := (arrangements keyLabels).map (·.map (·, ()))

/-- Every `Map`'s entries: up to three distinct keys, each holding value 0 or 1,
1 + 4 · 2 + 12 · 4 + 24 · 8 lists. -/
def maps : List (List (Nat × Nat)) :=
  (arrangementsUpTo 3 keyLabels).flatMap fun keys => (words keys.length [0, 1]).map keys.zip

/-- A write as its operation, `put` or `delete`, followed by the slots it writes. -/
def writeJson {β : Type} (slots : Nat × β → List Nat) : Write Nat β → Json
  | .put key value => .arr ((Json.str "put" :: (slots (key, value)).map toJson).toArray)
  | .delete key => .arr #[.str "delete", toJson key]

private structure Row where
  kind : String
  current : List (List Nat)
  next : List (List Nat)
  writes : List Json
  unchanged : Bool
  deriving ToJson

/-- What publication writes to a kept collection of `kind`, whose entries cross as `slots`. -/
private def row {β : Type} [DecidableEq β] (kind : String) (slots : Nat × β → List Nat)
    (current next : List (Nat × β)) : Row :=
  let walk := publish current next
  { kind, current := current.map slots, next := next.map slots,
    writes := walk.writes.map (writeJson slots), unchanged := walk.unchanged }

/-- Every pair of a `Set`'s current and next members, 65 · 65, then every pair of a `Map`'s
current and next entries, 249 · 249. -/
def run : IO Unit :=
  emitCorpus ((sets.flatMap fun current => sets.map fun next => Sum.inl (current, next)) ++
      (maps.flatMap fun current => maps.map fun next => Sum.inr (current, next)))
    fun
    | .inl (current, next) => row "set" (fun entry => [entry.1]) current next
    | .inr (current, next) => row "map" (fun entry => [entry.1, entry.2]) current next

end Reconcile.CollectionWritesOracle
