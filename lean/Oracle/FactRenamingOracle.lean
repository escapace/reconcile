import Graph.FactRenaming
import Lean

/-! Oracle for the `FactRenaming` family: for each history of fact and rule actions it checks
that renaming the facts by a permutation renames the observed queries and orders, over an
exhaustive small corpus with bounded 64-fact cases, or over the histories in a fixture file. -/

namespace Reconcile.FactRenamingOracle

open Reconcile.FactRenaming Reconcile.OnlineRequirements Lean

private def wire : Action → List Nat
  | .query fact => [0, fact]
  | .update (.require fact) => [1, fact]
  | .update (.imply source target) => [2, source, target]

private structure Input where
  size : Nat
  swaps : List (Nat × Nat)
  actions : List (List Nat)
  deriving ToJson

private structure Observation where
  input : Input
  renamed : List (List Nat)
  queries : List (Option Bool)
  orders : List (List Nat)
  mappedOrders : List (List Nat)
  deriving ToJson

private def parseAction : List Nat → Except String Action
  | [0, fact] => .ok (.query fact)
  | [1, fact] => .ok (.update (.require fact))
  | [2, source, target] => .ok (.update (.imply source target))
  | _ => .error "Expected query, require or implication action"

private def emit (input : Input) : IO Unit := do
  if input.size > 64 || input.actions.length > 512 || input.swaps.length > 64 ||
      !(input.swaps.all fun pair => pair.1 < input.size && pair.2 < input.size) ||
      !(input.actions.all fun entry => entry.tail.all (· < input.size)) then
    throw (IO.userError "Relabelling input exceeds declared finite bounds")
  let inputs ← IO.ofExcept (input.actions.mapM parseAction)
  let names : Renaming := input.swaps.foldl
    (fun names pair => names.trans (Equiv.swap pair.1 pair.2)) (Equiv.refl Nat)
  let renamed := inputs.map (action names)
  let before := observations input.size empty inputs
  let after := observations input.size empty renamed
  if after != before.map (fun entry => (entry.1, entry.2.map names)) then
    throw (IO.userError "Ordered relabelling witness failed")
  let result : Observation :=
    { input, renamed := renamed.map wire, queries := before.map Prod.fst,
      orders := before.map Prod.snd, mappedOrders := after.map Prod.snd }
  IO.println (toJson result).compress

private def words : Nat → List (List Nat) → List (List (List Nat))
  | 0, _ => [[]]
  | depth + 1, alphabet =>
    [] :: alphabet.flatMap fun letter => (words depth alphabet).map (letter :: ·)

private def alphabet (size : Nat) : List (List Nat) :=
  (List.range size).flatMap (fun fact => [[0, fact], [1, fact]]) ++
    (List.range size).flatMap fun source => (List.range size).map fun target => [2, source, target]

private def corpus : IO Unit := do
  let small := words 5 (alphabet 2)
  let three := words 3 (alphabet 3)
  IO.println (small.length + three.length + 4)
  for inputs in small do emit ⟨2, [(0, 1)], inputs⟩
  for inputs in three do emit ⟨3, [(0, 2), (1, 2)], inputs⟩
  emit ⟨0, [], []⟩
  let swaps := (List.range 32).map fun fact => (fact, 63 - fact)
  let cycle := (List.range 64).map fun fact => [2, fact, (fact + 1) % 64]
  emit ⟨64, swaps, cycle ++ [[0, 63], [1, 0], [0, 63]]⟩
  emit ⟨64, swaps, (List.range 64).map (fun fact => [0, fact]) ++ cycle ++ [[1, 63]]⟩
  emit ⟨64, swaps, [[1, 0]] ++ cycle ++ cycle ++ [[0, 63], [1, 0]]⟩

def run (args : List String) : IO Unit := do
  match args with
  | [] => corpus
  | _ => throw (IO.userError "Expected no argument")

end Reconcile.FactRenamingOracle
