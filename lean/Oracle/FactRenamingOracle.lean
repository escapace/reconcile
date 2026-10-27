import Graph.FactRenaming
import Oracle.Enumerate
import Oracle.Protocol

/-! Oracle for the `FactRenaming` family: for each history of fact and rule actions, the
observed queries and orders and those of the history with its facts renamed by a permutation,
which are the same queries and the renamed orders (`renamed_observations`), over an exhaustive
small corpus with bounded 64-fact cases. -/

namespace Reconcile.FactRenamingOracle

open Reconcile.FactRenaming Reconcile.OnlineRequirements Reconcile.Enumerate Reconcile.Protocol
  Lean

/-- Renaming the facts of the empty state leaves it empty. -/
theorem online_empty (names : Renaming) : online names empty = empty := by
  simp only [online, empty, Finset.image_empty, List.map_nil]
  rfl

/-- `observations_eq` from the empty state, where every row starts. -/
theorem renamed_observations (names : Renaming) (fuel : Nat) (inputs : List Action) :
    observations fuel empty (inputs.map (action names)) =
      (observations fuel empty inputs).map fun entry => (entry.1, entry.2.map names) := by
  simpa [online_empty] using observations_eq names fuel empty inputs

private def wire : Action → List Nat
  | .query fact => [0, fact]
  | .update (.require fact) => [1, fact]
  | .update (.imply source target) => [2, source, target]

private structure Observation where
  size : Nat
  actions : List (List Nat)
  renamed : List (List Nat)
  queries : List (Option Bool)
  orders : List (List Nat)
  mappedOrders : List (List Nat)
  deriving ToJson

/-- A history over `size` facts, with its facts renamed by the product of the transpositions
`swaps`. -/
private def observe : Nat × List (Nat × Nat) × List Action → Observation
  | (size, swaps, actions) =>
    let names : Renaming := swaps.foldl
      (fun names pair => names.trans (Equiv.swap pair.1 pair.2)) (Equiv.refl Nat)
    let renamed := actions.map (action names)
    let before := observations size empty actions
    { size, actions := actions.map wire, renamed := renamed.map wire,
      queries := before.map Prod.fst, orders := before.map Prod.snd,
      mappedOrders := (observations size empty renamed).map Prod.snd }

private def alphabet (size : Nat) : List Action :=
  (List.range size).flatMap (fun fact => [.query fact, .update (.require fact)]) ++
    (List.range size).flatMap fun source => (List.range size).map fun target =>
      .update (.imply source target)

def run : IO Unit := do
  let swaps := (List.range 32).map fun fact => (fact, 63 - fact)
  let cycle := (List.range 64).map fun fact => Action.update (.imply fact ((fact + 1) % 64))
  emitCorpus ((wordsUpTo 5 (alphabet 2)).map ((2, [(0, 1)], ·)) ++
    (wordsUpTo 3 (alphabet 3)).map ((3, [(0, 2), (1, 2)], ·)) ++
    [(0, [], []),
      (64, swaps, cycle ++ [.query 63, .update (.require 0), .query 63]),
      (64, swaps, (List.range 64).map Action.query ++ cycle ++ [.update (.require 63)]),
      (64, swaps, [.update (.require 0)] ++ cycle ++ cycle ++ [.query 63, .update (.require 0)])])
    observe

end Reconcile.FactRenamingOracle
