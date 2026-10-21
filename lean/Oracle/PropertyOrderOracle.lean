import Property.PropertyOrder
import Lean

/-! Oracle for the `PropertyOrder` family: exhaustive short traces of the reference and candidate
cursors of `PropertyOrder`, checking that they agree and that the candidate does no more checks,
and reporting the kept keys, cursor positions, retained count and checks. -/

namespace Reconcile.PropertyOrderOracle

open Reconcile.PropertyOrder Lean

private def alphabet : List Key :=
  [.index 0, .index 1, .name 0, .name 1, .symbol 0, .symbol 1]

private def permutationsUpTo : Nat → List Key → List (List Key)
  | 0, _ => [[]]
  | depth + 1, available =>
    [] :: available.flatMap (fun key =>
      (permutationsUpTo depth (available.erase key)).map (key :: ·))

private def wordsUpTo : Nat → List Key → List (List Key)
  | 0, _ => [[]]
  | depth + 1, letters =>
    [] :: letters.flatMap (fun key => (wordsUpTo depth letters).map (key :: ·))

private def encode : Key → Nat
  | .index label => 3 * label
  | .name label => 3 * label + 1
  | .symbol label => 3 * label + 2

private structure Observation where
  desired : List Nat
  current : List Nat
  keeps : List Bool
  name : Nat
  symbol : Int
  retained : Nat
  referenceChecks : Nat
  candidateChecks : Nat
  deriving ToJson

/-- Exhaustive short traces include absent keys, repeated misses and arbitrary
sector interleaving. The theorem covers finite inputs beyond this witness corpus. -/
def run : IO Unit := do
  let desiredCases := permutationsUpTo 3 alphabet
  let currents := wordsUpTo 3 (.name 2 :: alphabet)
  IO.println (desiredCases.length * currents.length)
  for desired in desiredCases do
    for current in currents do
      let before := initial desired
      let reference := runReference desired current before
      let candidate := runCandidate desired current before false
      if candidate.keeps != reference.keeps || candidate.cursor != reference.cursor ||
          candidate.checks > reference.checks then
        throw (IO.userError "Property-order model witness failed")
      let observation : Observation :=
        { desired := desired.map encode
          current := current.map encode
          keeps := reference.keeps
          name := desired.length - reference.cursor.names.length
          symbol := if before.symbols.isEmpty then -1
            else Int.ofNat (desired.length - reference.cursor.symbols.length)
          retained := reference.cursor.retained
          referenceChecks := reference.checks
          candidateChecks := candidate.checks }
      IO.println (toJson observation).compress

end Reconcile.PropertyOrderOracle
