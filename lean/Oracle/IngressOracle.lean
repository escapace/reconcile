import Types.Ingress
import Lean

/-! Oracle for the `Ingress` family: recognizes every built-in and listed prototype tail behind up
to two custom prototypes, with and without a typed-array brand, and behind a custom prototype whose
prototype read throws, with `Types.Ingress.ingress`. Each row reports the outcome and the reads of
the object itself with the prototype read shared and with a separate atom split, and the reads
through its kind's capture with that read passed on and with capture reading it again. -/

namespace Reconcile.IngressOracle

open Reconcile.Types Reconcile.Types.Ingress Lean

private def object : Proto := ⟨.object, .object⟩

/-- Real chains from a built-in prototype to `null`, in the order the bridge numbers them:
`null`, `Object.prototype`, `Date`, `Map`, `Set`, `ArrayBuffer` and `DataView`, `Uint8Array`
with `%TypedArray%`, `URL`, `URLSearchParams`, the listed `RegExp`, `Error`, `Promise` and `Blob`,
and `TypeError`, which inherits `Error`. Index 15 is a throwing read after the custom
prototypes. -/
def tails : List (List Proto) :=
  [[], [object]] ++
  (List.range 5).map (fun r => [⟨.data (r + 2), .builtin (r + 1)⟩, object]) ++
  [[⟨.data 7, .other 0⟩, ⟨.data 8, .builtin 6⟩, object], [⟨.data 9, .other 2⟩, object],
    [⟨.data 10, .other 3⟩, object]] ++
  ([0, 1, 6, 12].zip [4, 5, 6, 7]).map
    (fun (atom, other) => [⟨.listed atom, .other other⟩, object]) ++
  [[⟨.data 0, .other 8⟩, ⟨.listed 1, .other 5⟩, object], []]

def raisingTail : Nat := 15

/-- `URL.prototype` and `URLSearchParams.prototype` as the tails label them; no Temporal value
occurs. -/
def targets : RecognitionPlain.Targets := { temporal := [], url := .other 2, params := .other 3 }

private structure Observation where
  depth : Nat
  tail : Nat
  brand : Bool
  outcome : String
  rank : Nat
  shared : Nat
  separate : Nat
  captured : Nat
  capturedSeparate : Nat
  deriving ToJson

private def describe : Outcome → String × Nat
  | .structural r => ("structural", r)
  | .object => ("object", 10)
  | .atom => ("atom", 10)
  | .raised => ("raised", 0)

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
    let result := ingress .miss chain brand targets
    let (outcome, rank) := describe result
    IO.println (toJson ({
      depth, tail, brand, outcome, rank
      shared := ownReads true .miss chain brand targets
      separate := ownReads false .miss chain brand targets
      captured := ownReads true .miss chain brand targets + captureReads true .miss result
      capturedSeparate :=
        ownReads false .miss chain brand targets + captureReads false .miss result } :
      Observation)).compress

end Reconcile.IngressOracle
