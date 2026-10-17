import Serialization.Positional
import Serialization.Preorder
import Lean

open Lean SerializationPositional

/-!
# Positional wire oracle

Parses a runtime document over the bridge domain (records, null-prototype records, dense and
sparse arrays, JSON literals and shared scalar nodes), splits its control table with the proved
`decodeControl`, decodes it with the proved `decodeRelaxed`, `kindsOf`, `presentFrom` and the
`Preorder` numbering check, and re-emits it with `encodeDocument`, `encodeControl` and
`presenceRuns`. The TypeScript bridge requires the re-emitted document to equal every
`stringify` output, and requires accepted non-canonical documents to decode to the same graph
in Lean and at runtime.
Fixed-schema headers (a sparse array's length and presence runs, a bigint's digits) are split
from the slots by tag, as the runtime schema does.
-/

namespace Reconcile.SerializationOracle

abbrev E := Except String

def need {α : Type} (message : String) : Option α → E α
  | some a => .ok a
  | none => .error message

def scalar : Json → Bool
  | .arr _ => false
  | .obj _ => false
  | _ => true

abbrev Lit := {j : Json // scalar j = true}

instance : Inhabited Lit := ⟨⟨.null, rfl⟩⟩
instance : Inhabited (Node (List Nat) Lit) := ⟨⟨[], []⟩⟩

def natJson (i : Nat) : Json := .num (JsonNumber.fromNat i)

def ofNatJson : Json → Option Nat
  | .num ⟨m, 0⟩ => if 0 ≤ m then some m.toNat else none
  | _ => none

/-- The JSON value channel: a literal is any JSON scalar; a reference is a natural number. -/
def V : Values Lit Json where
  lit := Subtype.val
  nat := natJson
  ofLit := fun j => if h : scalar j = true then some ⟨j, h⟩ else none
  ofNat := ofNatJson
  ofLit_lit := fun s => by simp [s.property]
  ofNat_nat := fun i => by simp [natJson, ofNatJson, JsonNumber.fromNat]
  lit_ofLit := fun w s h => by
    by_cases hw : scalar w = true
    · simp only [hw, ↓reduceDIte, Option.some.injEq] at h; rw [← h]
    · simp [hw] at h
  nat_ofNat := fun w i h => by
    unfold ofNatJson at h
    split at h
    · rename_i m
      split at h
      · rename_i hm
        cases h
        simp [natJson, JsonNumber.fromNat, Int.toNat_of_nonneg hm]
      · cases h
    · cases h

def nat (j : Json) : E Nat := need "natural number required" (ofNatJson j)
def nats (j : Json) : E (List Nat) := do (← j.getArr?).toList.mapM nat
def strings (j : Json) : E (List String) := do (← j.getArr?).toList.mapM Json.getStr?

def maxArrayLength : Nat := 4294967295

/-- Layout key width by tag: records carry a shape id; arrays and shared scalars only a tag. -/
def keyWidth (tag : Nat) : E Nat :=
  if tag ≤ 1 then pure 2
  else if tag ≤ 3 ∨ (13 ≤ tag ∧ tag ≤ 18) then pure 1
  else throw "tag outside the bridge domain"

/-- Payload header and slots by tag. -/
def split (tag : Nat) (payload : Json) : E (List Json × List Json) := do
  let a := (← payload.getArr?).toList
  if tag == 3 then
    match a with
    | [length, presence, values] => return ([length, presence], (← values.getArr?).toList)
    | _ => throw "sparse array"
  if tag == 18 then return (a, [])
  return ([], a)

def scalarName (tag : Nat) : String :=
  match tag with
  | 13 => "undefined" | 14 => "NaN" | 15 => "Infinity" | 16 => "-Infinity" | _ => "-0"

def atom (j : Json) : Json := toJson ([toJson (0 : Nat), toJson j.compress] : List Json)

structure Parsed where
  shapes : List (List String)
  layouts : List (List Nat × List Nat)
  descriptors : List Nat
  headers : List (List Json)
  nodes : List (Node (List Nat) Lit)

def parseDocument (wire : Json) : E Parsed := do
  let doc ← wire.getArr?
  if doc.size != 2 then throw "envelope"
  let payloads ← (← doc[1]!.getArr?).toList.mapM pure
  if payloads.isEmpty then throw "envelope"
  -- Executes the proved control framing (decode_encode_control, encode_decode_control).
  let (descriptors, shapeJson, layoutJson) ←
    need "control" (decodeControl V payloads.length (← doc[0]!.getArr?).toList)
  let shapes ← shapeJson.mapM fun keys => keys.mapM Json.getStr?
  let layouts ← layoutJson.mapM fun j => do
    let flat ← j.mapM nat
    let tag ← need "layout" flat.head?
    let width ← keyWidth tag
    if flat.length < width then throw "layout key"
    if tag ≤ 1 && flat[1]! ≥ shapes.length then throw "shape reference"
    pure (flat.take width, flat.drop width)
  let split ← (descriptors.zip payloads).mapM fun (d, p) => do
    let (key, _) ← need "layout id" layouts[d]?
    split key.head! p
  let document : Document (List Nat) Json := ⟨layouts, descriptors, split.map Prod.snd⟩
  -- Executes the proved relaxed decoder: canonical runs and bounded references, tables as given.
  let nodes ← need "positional decode" (decodeRelaxed V document)
  return ⟨shapes, layouts, descriptors, split.map Prod.fst, nodes⟩

def bigintText (text : String) : Bool :=
  match text.toList with
  | ['0'] => true
  | '-' :: d :: _ => d != '0' && (text.drop 1).all Char.isDigit
  | d :: _ => d != '0' && text.all Char.isDigit
  | [] => false

/-- Checks each node's fixed-schema header and returns the node's tag, shape id, and the
sparse length and present positions when it has them. -/
def checkHeader (shapes : List (List String)) (v : Node (List Nat) Lit) (header : List Json) :
    E (Option (Nat × List Nat)) := do
  let tag := v.key.head!
  if tag ≤ 1 then
    let keys ← need "shape" shapes[v.key[1]!]?
    if keys.length != v.slots.length then throw "record arity"
    return none
  if tag == 2 then return none
  if tag == 3 then
    let length ← nat header[0]!
    if length > maxArrayLength then throw "array length"
    let presence ← nats header[1]!
    if presence.isEmpty then throw "sparse array without a hole"
    -- Executes the proved presence decoding (sparse_canonical).
    let kinds ← need "presence" (kindsOf presence length)
    let positions := presentFrom kinds 0
    if positions.length != v.slots.length then throw "sparse values"
    return some (length, positions)
  if tag == 18 then
    match header with
    | [.str text] => if bigintText text then return none else throw "bigint"
    | _ => throw "bigint"
  if !header.isEmpty ∨ !v.slots.isEmpty then throw "scalar"
  return none

/-- Defining a repeated key keeps its first position and its last value, as the runtime's
property definitions do. -/
def foldKeys (es : List (String × Json)) : List (String × Json) :=
  es.foldl (fun acc (k, v) =>
    if acc.any (·.1 == k) then acc.map fun (k', v') => (k', if k' == k then v else v')
    else acc ++ [(k, v)]) []

def kindText (tag : Nat) : String := if tag == 0 then "object" else if tag == 1 then "nullObject"
  else "array"

def evaluate (request : Json) : E Json := do
  let wire ← request.getObjVal? "wire"
  let doc ← wire.getArr?
  if doc.size == 1 then
    if !scalar doc[0]! then throw "literal"
    return Json.mkObj [("ok", toJson true), ("expanded", Json.mkObj [("root", atom doc[0]!),
      ("rows", toJson ([] : List Json))]), ("reemitted", wire)]
  let parsed ← parseDocument wire
  let infos ← (parsed.nodes.zip parsed.headers).mapM fun (v, h) => checkHeader parsed.shapes v h
  -- Executes the proved numbering check (Preorder.lean check_iff) on the reference graph.
  let children : SerializationDFS.Graph := fun v =>
    (parsed.nodes.getD v ⟨[], []⟩).slots.filterMap fun s => match s with
      | .ref i => some i
      | .lit _ => none
  if !SerializationPreorder.check children parsed.nodes.length then throw "node order"
  let tags := parsed.nodes.map fun v => v.key.head!
  -- Container nodes become model rows, renumbered among themselves; scalar nodes become atoms.
  let containers := (List.range tags.length).filter fun i => tags[i]! ≤ 3
  let token := fun (s : Slot Lit) => match s with
    | .lit j => atom j.val
    | .ref i =>
      let tag := tags[i]!
      if tag ≤ 3 then toJson ([toJson (1 : Nat), toJson (containers.idxOf i)] : List Json)
      else if tag == 18 then
        atom (Json.mkObj [("bigint", (parsed.headers[i]!)[0]!)])
      else atom (Json.mkObj [("scalar", toJson (scalarName tag))])
  let mut rows : List Json := []
  for i in containers do
    let v := parsed.nodes[i]!
    let tag := tags[i]!
    let (payload, keys) ← match infos[i]! with
      | some (length, positions) => pure ([toString length], positions.map toString)
      | none =>
        if tag ≤ 1 then pure ([], parsed.shapes[v.key[1]!]!)
        else pure ([toString v.slots.length], (List.range v.slots.length).map toString)
    rows := rows ++ [Json.mkObj [("kind", toJson (kindText tag)), ("payload", toJson payload),
      ("edges", toJson ((foldKeys ((keys.zip v.slots).map fun (k, s) => (k, token s))).map
        fun (k, t) => toJson [toJson k, t]))]]
  let root := token (.ref 0)
  -- Re-emit with the proved encoder and reattach the fixed-schema headers.
  let encoded := encodeDocument V parsed.nodes
  let layouts := encoded.layouts.map fun (key, runs) => (key ++ runs).map natJson
  let payloads := (List.range encoded.payloads.length).map fun i =>
    let slots := encoded.payloads[i]!
    match infos[i]! with
    | some (length, positions) =>
      Json.arr #[toJson length, toJson (presenceRuns positions length), Json.arr slots.toArray]
    | none => Json.arr (parsed.headers[i]! ++ slots).toArray
  let control := encodeControl V encoded.descriptors (parsed.shapes.map (·.map toJson))
    layouts
  let reemitted := toJson [Json.arr control.toArray, Json.arr payloads.toArray]
  return Json.mkObj [("ok", toJson true), ("expanded", Json.mkObj [("root", root),
    ("rows", toJson rows)]), ("reemitted", reemitted)]

def run (input : String) : IO Unit := do
  let requests ← IO.ofExcept (Json.parse input >>= Json.getArr?)
  let responses := requests.map fun request =>
    match evaluate request with
    | .ok result => result
    | .error error => Json.mkObj [("ok", toJson false), ("error", toJson error)]
  let output := ((Json.arr responses).compress.replace " " "\\u2028").replace " " "\\u2029"
  (← IO.getStdout).putStrLn output

end Reconcile.SerializationOracle
