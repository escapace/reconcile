import Produce.DraftIteration
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `DraftIteration` family: runs every script of one to three iterations and
writes on a `Map` draft through `DraftIteration`, reporting each walk, the result's entries and
whether the result keeps the original. -/

namespace Reconcile.DraftIterationOracle

open Reconcile.DraftIteration Reconcile.Enumerate Reconcile.Protocol Lean

/-- Recipe steps: iterate, write an equal value, change a value, add an entry, delete an entry,
delete a missing key. -/
private def step : Nat → Draft → Draft × Option (List (Nat × Nat))
  | 0, d => let r := iterate d; (r.1, some r.2)
  | 1, d => (set 1 10 d, none)
  | 2, d => (set 1 11 d, none)
  | 3, d => (set 3 30 d, none)
  | 4, d => (delete 2 d, none)
  | _, d => (delete 9 d, none)

private def scripts : List (List Nat) := (wordsUpTo 3 (List.range 6)).tail

private structure Observation where
  steps : List Nat
  iterations : List (List (List Nat))
  entries : List (List Nat)
  kept : Bool
  deriving ToJson

private def pairs (entries : List (Nat × Nat)) : List (List Nat) := entries.map fun (k, v) => [k, v]

/-- Every script of one to three steps on a draft of `[(1, 10), (2, 20)]`: what each iteration
walked, the result's entries and whether the result keeps the original. -/
def run : IO Unit :=
  emitCorpus scripts fun steps =>
    let start : Draft := { base := [(1, 10), (2, 20)], copy := none, modified := false }
    let (final, iterations) := steps.foldl (init := (start, ([] : List (List (List Nat)))))
      fun (d, seen) s =>
        let (d', walked) := step s d
        (d', match walked with | some e => seen ++ [pairs e] | none => seen)
    ({ steps, iterations, entries := pairs (source final), kept := kept final } : Observation)

end Reconcile.DraftIterationOracle
