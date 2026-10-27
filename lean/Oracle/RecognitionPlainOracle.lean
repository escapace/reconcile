import Types.RecognitionPlain
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `RecognitionPlain` family: recognizes every built-in prototype tail behind up to
two custom prototypes, without a view brand and as a typed array or a `DataView`, each over a
recognized buffer, over one whose prototype was replaced and over one whose prototype's read
throws, and behind a custom prototype whose prototype read throws, with
`Types.RecognitionPlain.recognize`. Each row reports the full recognition, the answer of each
known-kind check and whether it raises, and whether one read decides the object. -/

namespace Reconcile.RecognitionPlainOracle

open Reconcile.Types.RecognitionPlain Reconcile.Enumerate Reconcile.Protocol Lean

/-- Real chains from a built-in prototype to `null`, in the order the bridge numbers them:
`null`, `Object.prototype`, `Date`, `Map`, `Set`, `ArrayBuffer` and `DataView`, then
`Uint8Array` with `%TypedArray%`, `URL` and `URLSearchParams`. Index 10 is a throwing read after
the custom prototypes. -/
def tails : List (List Proto) :=
  [[], [.object]] ++ (List.range 5).map (fun r => [.builtin (r + 1), .object]) ++
  [[.other 0, .builtin 6, .object], [.other 2, .object], [.other 3, .object], []]

def raisingTail : Nat := 10

/-- `URL.prototype` and `URLSearchParams.prototype` as the tails label them, and
`SharedArrayBuffer.prototype`, which no buffer's chain holds; no Temporal value occurs. -/
def targets : Targets := { temporal := [], url := .other 2, params := .other 3, shared := [.other 9] }

/-- A view's buffer's chain: recognized (`ArrayBuffer.prototype`), replaced by `null`, or a
prototype whose own prototype read throws. -/
def buffer (foreign raises : Bool) : Chain :=
  if raises then { protos := [.other 10], raises := true }
  else if foreign then { protos := [], raises := false }
  else { protos := [.builtin 4, .object], raises := false }

/-- Every tail behind zero to two custom prototypes with every view, less a branded object
directly on the throwing tail: a branded object cannot throw on its own read. -/
def viewCases {V : Type} (tails raisingTail : Nat) (views : List V) (branded : V → Bool) :
    List (Nat × Nat × V) :=
  (List.range 3).flatMap fun depth => (List.range tails).flatMap fun tail =>
    (views.filter fun view => !(branded view && depth = 0 && tail = raisingTail)).map
      (depth, tail, ·)

private structure Observation where
  depth : Nat
  tail : Nat
  brand : Bool
  typed : Bool
  foreign : Bool
  bufferRaises : Bool
  plain : Bool
  selected : Int
  raised : Bool
  known : List Bool
  knownRaised : List Bool
  deriving ToJson

/-- The recognition of an object behind `depth` custom prototypes over tail `tail`, with the view
brand, the typed-array brand, whether the buffer is foreign and whether its chain raises. -/
private def observe : Nat × Nat × Bool × Bool × Bool × Bool → Observation
  | (depth, tail, brand, typed, foreign, bufferRaises) =>
    let chain : Chain :=
      { protos := behind Proto.other depth (tails.getD tail []), raises := tail = raisingTail }
    let b := buffer foreign bufferRaises
    let full := outcome (recognize 10 .miss chain brand typed b targets)
    let bounded := (List.range 10).map fun r =>
      outcome (recognize (r + 1) .miss chain brand typed b targets)
    { depth, tail, brand, typed, foreign, bufferRaises
      plain := Types.RecognitionPlain.plain chain
      selected := match full.1 with | some r => (r : Int) | none => -1
      raised := full.2.isSome
      known := (List.range 10).zipWith (fun r o => decide (o = (some (r + 1), none))) bounded
      knownRaised := bounded.map (·.2.isSome) }

/-- Each tail behind zero to two custom prototypes with each view: none, then a typed array and a
`DataView`, each over a recognized, a foreign and a raising buffer. -/
def run : IO Unit :=
  emitCorpus (viewCases tails.length raisingTail [(false, false, false, false),
    (true, true, false, false), (true, true, true, false), (true, true, false, true),
    (true, false, false, false), (true, false, true, false), (true, false, false, true)]
    (·.1)) observe

end Reconcile.RecognitionPlainOracle
