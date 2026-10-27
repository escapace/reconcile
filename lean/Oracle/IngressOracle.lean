import Types.Ingress
import Oracle.RecognitionPlainOracle
import Lean

/-! Oracle for the `Ingress` family: recognizes every built-in and listed prototype tail behind up
to two custom prototypes, with and without a typed-array brand, and behind a custom prototype whose
prototype read throws, with `Types.Ingress.ingress`. Each row reports the outcome and the reads of
the object itself with the prototype read shared and with a separate atom split. -/

namespace Reconcile.IngressOracle

open Reconcile.Types Reconcile.Types.Ingress Lean

private def object : Proto := ⟨.object, .object⟩

/-- A prototype of the RecognitionPlain bridge's chains, which no atom constructor's chain
holds: `Object.prototype`, or a data prototype with its own label. -/
private def unlisted : RecognitionPlain.Proto → Proto
  | .object => object
  | .builtin rank => ⟨.data rank, .builtin rank⟩
  | .other label => ⟨.data (20 + label), .other label⟩

/-- Real chains from a built-in prototype to `null`, in the order the bridge numbers them: the
RecognitionPlain bridge's chains before its throwing read (`null`, `Object.prototype`, `Date`,
`Map`, `Set`, `ArrayBuffer`, `DataView`, `Uint8Array` with `%TypedArray%`, `URL` and
`URLSearchParams`), then the listed `RegExp`, `Error`, `Promise` and `Blob`, and `TypeError`,
which inherits `Error`. Index 15 is a throwing read after the custom prototypes. -/
def tails : List (List Proto) :=
  (RecognitionPlainOracle.tails.take RecognitionPlainOracle.raisingTail).map (·.map unlisted) ++
  ([0, 1, 6, 12].zip [4, 5, 6, 7]).map
    (fun (atom, other) => [⟨.listed atom, .other other⟩, object]) ++
  [[⟨.data 0, .other 8⟩, ⟨.listed 1, .other 5⟩, object], []]

def raisingTail : Nat := 15

private structure Observation where
  depth : Nat
  tail : Nat
  brand : Bool
  outcome : String
  rank : Nat
  shared : Nat
  separate : Nat
  deriving ToJson

private def describe : Option Atoms.Ingress → String × Nat
  | some (.structural r) => ("structural", r)
  | some .object => ("object", 10)
  | some .atom => ("atom", 10)
  | none => ("raised", 0)

def run : IO Unit := do
  let cases := (List.range 3).flatMap fun depth => (List.range tails.length).flatMap fun tail =>
    ([false, true].filter fun brand => !(brand && depth = 0 && tail = raisingTail)).map
      (depth, tail, ·)
  IO.println cases.length
  for (depth, tail, brand) in cases do
    let chain : Chain := {
      protos := (List.range depth).map (fun l => ⟨.data (100 + l), .other (100 + l)⟩) ++
        tails.getD tail []
      raises := tail = raisingTail }
    let targets := RecognitionPlainOracle.targets
    let (outcome, rank) := describe (ingress .miss chain brand targets)
    IO.println (toJson ({
      depth, tail, brand, outcome, rank
      shared := ownReads true .miss chain brand targets
      separate := ownReads false .miss chain brand targets } : Observation)).compress

end Reconcile.IngressOracle
