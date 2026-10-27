import Types.Atoms
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `Atoms` family: classifies every built-in prototype tail behind up to three
custom prototypes with `Types.Atoms.classify`, reporting whether the chain is atomic and how many
reads the walk makes. -/

namespace Reconcile.AtomsOracle

open Reconcile.Types.Atoms Reconcile.Enumerate Reconcile.Protocol Lean

/-- Real chains from a built-in prototype to `null`, in the order the bridge numbers them:
`null`, `Object.prototype`, `Array.prototype`, the fourteen listed prototypes (`RegExp`,
`Error`, `WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`, `Promise`, `Number`,
`String`, `Boolean`, `BigInt`, `Symbol`, `Blob`, `SharedArrayBuffer`), then `TypeError` and
`File`, which inherit listed prototypes, and the data prototypes `Map`, `Set`, `Date`, `URL` and
`Uint8Array`. -/
def tails : List Chain :=
  [[], [.object], [.array, .object]] ++
  (List.range 14).map (fun label => [.listed label, .object]) ++
  [[.data 0, .listed 1, .object], [.data 1, .listed 12, .object]] ++
  (List.range 4).map (fun label => [.data (label + 2), .object]) ++
  [[.data 6, .data 7, .object]]

private structure Observation where
  depth : Nat
  tail : Nat
  atomic : Bool
  reads : Nat
  deriving ToJson

/-- Every tail behind up to three custom prototypes, with the walk's answer and reads. -/
def run : IO Unit :=
  emitCorpus ((List.range 4).flatMap fun depth => (List.range tails.length).map (depth, ·))
    fun (depth, tail) =>
      let (atomic, reads) := classify (behind Proto.data depth (tails.getD tail []))
      ({ depth, tail, atomic, reads } : Observation)

end Reconcile.AtomsOracle
