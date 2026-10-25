import Types.RecognitionPlain
import Lean

/-! Oracle for the `RecognitionPlain` family: recognizes every built-in prototype tail behind up to
two custom prototypes, with and without a view brand, a branded object over a recognized buffer
and over one whose prototype was replaced, and behind a custom prototype whose prototype read
throws, with `Types.RecognitionPlain.recognize`. Each row reports the full
recognition, the answer of each known-kind check and whether one read decides the object. -/

namespace Reconcile.RecognitionPlainOracle

open Reconcile.Types.Recognition Reconcile.Types.RecognitionPlain Lean

/-- Real chains from a built-in prototype to `null`, in the order the bridge numbers them:
`null`, `Object.prototype`, `Date`, `Map`, `Set`, `ArrayBuffer` and `DataView`, then
`Uint8Array` with `%TypedArray%`, `URL` and `URLSearchParams`. Index 10 is a throwing read after
the custom prototypes. -/
def tails : List (List Proto) :=
  [[], [.object]] ++ (List.range 5).map (fun r => [.builtin (r + 1), .object]) ++
  [[.other 0, .other 1, .object], [.other 2, .object], [.other 3, .object], []]

def raisingTail : Nat := 10

/-- `URL.prototype` and `URLSearchParams.prototype` as the tails label them; no Temporal value
occurs. -/
def targets : Targets := { temporal := [], url := .other 2, params := .other 3 }

private structure Observation where
  depth : Nat
  tail : Nat
  brand : Bool
  foreign : Bool
  plain : Bool
  selected : Int
  raised : Bool
  known : List Bool
  deriving ToJson

def run : IO Unit := do
  let views := [(false, false), (true, false), (true, true)]
  let cases := (List.range 3).flatMap fun depth => (List.range tails.length).flatMap fun tail =>
    (views.filter fun (brand, _) => !(brand && depth = 0 && tail = raisingTail)).map
      fun (brand, foreign) => (depth, tail, brand, foreign)
  IO.println cases.length
  for (depth, tail, brand, foreign) in cases do
    let chain : Chain := {
      protos := (List.range depth).map (fun label => Proto.other (100 + label)) ++
        tails.getD tail []
      raises := tail = raisingTail }
    let full := outcome (recognize 10 .miss chain brand foreign targets)
    let known := (List.range 10).map fun r =>
      decide (outcome (recognize (r + 1) .miss chain brand foreign targets) = (some (r + 1), none))
    IO.println (toJson ({
      depth, tail, brand, foreign
      plain := Types.RecognitionPlain.plain chain brand
      selected := match full.1 with | some r => (r : Int) | none => -1
      raised := full.2.isSome
      known } : Observation)).compress

end Reconcile.RecognitionPlainOracle
