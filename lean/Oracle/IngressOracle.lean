import Types.Ingress
import Oracle.RecognitionPlainOracle

/-! Oracle for the `Ingress` family: recognizes every built-in and listed prototype tail behind up
to two custom prototypes, without a typed-array brand and as a typed array over a recognized
buffer, over one whose prototype was replaced and over one whose prototype's read throws, and
behind a custom prototype whose prototype read throws, with `Types.Ingress.ingress`. Each row
reports the outcome and the reads of the object itself with the prototype read shared and with a
separate atom split. -/

namespace Reconcile.IngressOracle

open Reconcile.Types Reconcile.Types.Ingress Reconcile.Enumerate Reconcile.Protocol Lean

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
  foreign : Bool
  bufferRaises : Bool
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

/-- The ingress of an object behind `depth` custom prototypes over tail `tail`, with the
typed-array brand, whether the buffer is foreign and whether its chain raises. -/
private def observe : Nat × Nat × Bool × Bool × Bool → Observation
  | (depth, tail, brand, foreign, bufferRaises) =>
    let chain : Chain :=
      { protos := behind (fun label => ⟨.data label, .other label⟩) depth (tails.getD tail [])
        raises := tail = raisingTail }
    let targets := RecognitionPlainOracle.targets
    let b := RecognitionPlainOracle.buffer foreign bufferRaises
    let (outcome, rank) := describe (ingress .miss chain brand b targets)
    { depth, tail, brand, foreign, bufferRaises, outcome, rank
      shared := ownReads true .miss chain brand b targets
      separate := ownReads false .miss chain brand b targets }

/-- Each tail behind zero to two custom prototypes with each view: none, then a typed array over a
recognized, a foreign and a raising buffer. -/
def run : IO Unit :=
  emitCorpus (RecognitionPlainOracle.viewCases tails.length raisingTail
    [(false, false, false), (true, false, false), (true, true, false), (true, false, true)]
    (·.1)) observe

end Reconcile.IngressOracle
