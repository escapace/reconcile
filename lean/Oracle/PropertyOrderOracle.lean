import Property.PropertyOrder
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `PropertyOrder` family: exhaustive short traces of the reference and candidate
cursors of `PropertyOrder`, which agree and where the candidate does no more checks
(`stream_equivalence`), reporting the kept keys, cursor positions, retained count and checks. -/

namespace Reconcile.PropertyOrderOracle

open Reconcile.PropertyOrder Reconcile.Enumerate Reconcile.Protocol Lean

private def alphabet : List Key :=
  [.index 0, .index 1, .name 0, .name 1, .symbol 0, .symbol 1]

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

private def observe : List Key × List Key → Observation
  | (desired, current) =>
    let before := initial desired
    let reference := runReference desired current before
    { desired := desired.map keyCode
      current := current.map keyCode
      keeps := reference.keeps
      name := desired.length - reference.cursor.names.length
      symbol := if before.symbols.isEmpty then -1
        else Int.ofNat (desired.length - reference.cursor.symbols.length)
      retained := reference.cursor.retained
      referenceChecks := reference.checks
      candidateChecks := (runCandidate desired current before false).checks }

/-- Exhaustive short traces include absent keys, repeated misses and arbitrary
sector interleaving. The theorem covers finite inputs beyond this witness corpus. -/
def run : IO Unit :=
  emitCorpus ((arrangementsUpTo 3 alphabet).flatMap fun desired =>
    (wordsUpTo 3 (.name 2 :: alphabet)).map (desired, ·)) observe

end Reconcile.PropertyOrderOracle
