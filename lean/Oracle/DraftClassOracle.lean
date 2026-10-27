import Produce.DraftClass
import Oracle.Protocol

/-! Oracle for the `DraftClass` family: for a `Map` and a `Set` draft, each a built-in and a
subclass instance, the prototype that owns every name on the draft's chain and the result of
`instanceof` for every prototype, as `DraftClass` gives them. -/

namespace Reconcile.DraftClassOracle

open Reconcile.DraftClass Reconcile.Protocol Lean

/-- Prototype identifiers: `Object.prototype`, `Map.prototype`, `Set.prototype`, a subclass of
each, and the draft layer. -/
private def objectProto : Nat := 0
private def subclassProto (map : Bool) : Nat := if map then 3 else 4
private def builtinProto (map : Bool) : Nat := if map then 1 else 2
private def layer : Nat := 9

private def collectionMethods (map : Bool) : List String :=
  (if map then ["get", "set"] else
    ["add", "union", "intersection", "difference", "symmetricDifference", "isSubsetOf",
      "isSupersetOf", "isDisjointFrom"]) ++
    ["has", "delete", "clear", "size", "entries", "forEach", "keys", "values", "iterator"]

/-- Each subclass adds `custom` and overrides `has`; the built-in defines its methods and
`toStringTag`. -/
private def own (p : Nat) (n : String) : Option Nat :=
  if p = 1 && (n ∈ collectionMethods true || n = "toStringTag") then some p
  else if p = 2 && (n ∈ collectionMethods false || n = "toStringTag") then some p
  else if (p = 3 || p = 4) && (n = "custom" || n = "has") then some p
  else none

private def sourceChain (map subclass : Bool) : List Nat :=
  (if subclass then [subclassProto map] else []) ++ [builtinProto map, objectProto]

private structure Resolution where
  map : Bool
  subclass : Bool
  name : String
  /-- The prototype that defines the name on the draft's chain, or none. -/
  owner : Option Nat
  deriving ToJson

private structure Instance where
  map : Bool
  subclass : Bool
  proto : Nat
  isInstance : Bool
  deriving ToJson

private def names (map : Bool) : List String :=
  collectionMethods map ++ ["toStringTag", "custom"]

/-- On the draft of a `Map` or a `Set`, built-in or a subclass instance: the owner of a name, or
`instanceof` a prototype. -/
private def observe : Bool × Bool × (String ⊕ Nat) → Json
  | (map, subclass, query) =>
    let chain := draftChain layer (sourceChain map subclass)
    match query with
    | .inl name =>
      let owner := lookup (withLayer layer (collectionMethods map) (fun _ => layer) own) chain name
      toJson ({ map, subclass, name, owner } : Resolution)
    | .inr proto =>
      toJson ({ map, subclass, proto, isInstance := instanceOf chain proto } : Instance)

/-- For a `Map` and a `Set`, each as a built-in and a subclass instance: the owner of every name
on the draft's chain (`9` is the draft layer), then `instanceof` for every prototype. -/
def run : IO Unit :=
  let flags := [false, true]
  emitCorpus (flags.flatMap fun map => flags.flatMap fun subclass =>
    ((names map).map Sum.inl ++ [0, 1, 2, 3, 4].map Sum.inr).map (map, subclass, ·)) observe

end Reconcile.DraftClassOracle
