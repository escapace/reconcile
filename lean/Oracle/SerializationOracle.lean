import Serialization.Positional
import Serialization.Preorder
import Serialization.Size
import Lean

/-! Oracle for the `Serialization` family: parses a `serialize` document, checks its headers and
preorder numbering, expands it to model rows and re-emits it with the proved positional encoder,
reporting the expansion, the re-emitted document and its size in words. -/

open Lean SerializationPositional

/-!
# Positional wire oracle

Parses a runtime document over the bridge domain (records, null-prototype records, dense and
sparse arrays, JSON literals including objects and arrays, and shared scalar nodes), splits its control table with the proved
`decodeControl`, decodes it with the proved `decodeRelaxed`, `kindsOf`, `presentFrom` and the
`Preorder` numbering check, and re-emits it with `encodeDocument`, `encodeControl` and
`presenceRuns`. The TypeScript bridge requires the re-emitted document to equal every
`serialize` output, and requires accepted non-canonical documents to decode to the same graph
in Lean and at runtime. Each response also carries the document's size in words, computed with
`Size.lean`'s `accounting` and charge table (`tableCharges`) over the decoded nodes, which the
runtime must accept at exactly eight bytes per word.
Fixed-schema headers (a sparse array's length and presence runs, a bigint's digits) are split
from the slots by tag, as the runtime schema does.
-/

namespace Reconcile.SerializationOracle

abbrev E := Except String

def need {α : Type} (message : String) : Option α → E α
  | some a => .ok a
  | none => .error message

/-- A literal slot holds any JSON value, taken as JSON.parse produced it. -/
abbrev Lit := Json

instance : Inhabited (Node (List Nat) Lit) := ⟨⟨[], []⟩⟩

def natJson (i : Nat) : Json := .num (JsonNumber.fromNat i)

def ofNatJson : Json → Option Nat
  | .num ⟨m, 0⟩ => if 0 ≤ m then some m.toNat else none
  | _ => none

/-- The JSON value channel: a literal is any JSON value; a reference is a natural number. -/
def V : Values Lit Json where
  lit := id
  nat := natJson
  ofLit := some
  ofNat := ofNatJson
  ofLit_lit := fun _ => rfl
  ofNat_nat := fun i => by simp [natJson, ofNatJson, JsonNumber.fromNat]
  lit_ofLit := fun _ _ h => by cases h; rfl
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

/-- Bigint text as `Size.lean` reads it: an optional `-`, then `0x` and digits, each a decimal
digit or a lowercase letter up to `f`; none for any other text. -/
def parseBigint (text : String) : Option (Bool × List Nat) :=
  let hexDigit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let (negative, rest) := match text.toList with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  match rest with
  | '0' :: 'x' :: digits => (digits.mapM hexDigit).map (negative, ·)
  | _ => none

/-- Canonical bigint text: `Size.lean`'s `CanonicalInt`, which `encodeInt_decodeInt` proves
canonical: no leading zero, and `-0x0` is not one. -/
def bigintText (text : String) : Bool :=
  match parseBigint text with
  | some parsed => decide (SerializationSize.CanonicalInt parsed)
  | none => false

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

/-- A JSON object or array in a literal slot decodes to a fresh value referenced only there. It
expands to model rows numbered from `base` in completion order; Lean's object model orders keys,
so the bridge's composite literals use keys already in that order. -/
partial def expandLit (base : Nat) : Json → StateM (Array Json) Json
  | .arr items => do
    let mut edges : Array Json := #[]
    for i in [0:items.size] do
      edges := edges.push (toJson [toJson (toString i), ← expandLit base items[i]!])
    pushRow base "array" [toString items.size] edges
  | .obj kvs => do
    let mut edges : Array Json := #[]
    for (k, j) in kvs.toList do
      edges := edges.push (toJson [toJson k, ← expandLit base j])
    pushRow base "object" [] edges
  | j => pure (atom j)
where
  pushRow (base : Nat) (kind : String) (payload : List String) (edges : Array Json) :
      StateM (Array Json) Json := do
    let rows ← get
    set (rows.push (Json.mkObj [("kind", toJson kind), ("payload", toJson payload),
      ("edges", Json.arr edges)]))
    return toJson ([toJson (1 : Nat), toJson (base + rows.size)] : List Json)

/-! ## Size -/

/-- A string's length in UTF-16 code units, as JavaScript counts it. -/
def utf16Length (s : String) : Nat := s.toList.foldl (fun n c => n + if c.val > 0xFFFF then 2 else 1) 0

instance : Inhabited SerializationSize.Json := ⟨.null⟩

/-- A JSON literal as `Size.lean` measures it. -/
partial def sizeJson : Json → SerializationSize.Json
  | .null => .null
  | .bool b => .bool b
  | .num _ => .num
  | .str s => .str (utf16Length s)
  | .arr items => .arr (items.toList.map sizeJson)
  | .obj kvs => .obj (kvs.toList.map fun (k, v) => (utf16Length k, sizeJson v))

/-- The words of a literal where it occurs (`Size.lean` `words`). -/
def literalWords (j : Json) : Nat := SerializationSize.words (sizeJson j)

/-- What `Size.lean`'s charge table reads of node `i`: its tag, its shape's keys, its slots, a
sparse array's length, its literals' words and a bigint's digits. -/
def tableNode (shapes : List (List String)) (nodes : List (Node (List Nat) Lit))
    (headers : List (List Json)) (infos : List (Option (Nat × List Nat))) (i : Nat) :
    SerializationSize.TableNode :=
  let v := nodes.getD i ⟨[], []⟩
  let tag := v.key.headD 0
  { tag
    keys := if tag ≤ 1 then (shapes.getD (v.key.getD 1 0) []).map utf16Length else []
    slots := v.slots.length
    length := ((infos.getD i none).map Prod.fst).getD 0
    literals := (v.slots.map fun s => match s with
      | .lit j => literalWords j
      | .ref _ => 0).sum
    digits := match (headers.getD i []).headD .null with
      | .str text => ((parseBigint text).map Prod.snd).getD []
      | _ => [] }

def kindText (tag : Nat) : String := if tag == 0 then "object" else if tag == 1 then "nullObject"
  else "array"

def evaluate (request : Json) : E Json := do
  let wire ← request.getObjVal? "wire"
  let doc ← wire.getArr?
  if doc.size == 1 then
    let (root, rows) := (expandLit 0 doc[0]!).run #[]
    return Json.mkObj [("ok", toJson true), ("expanded", Json.mkObj [("root", root),
      ("rows", toJson rows)]), ("reemitted", wire), ("words", toJson (1 + literalWords doc[0]!))]
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
    | .lit j => expandLit containers.length j
    | .ref i => pure <|
      let tag := tags[i]!
      if tag ≤ 3 then toJson ([toJson (1 : Nat), toJson (containers.idxOf i)] : List Json)
      else if tag == 18 then
        atom (Json.mkObj [("bigint", (parsed.headers[i]!)[0]!)])
      else atom (Json.mkObj [("scalar", toJson (scalarName tag))])
  let mut rows : List Json := []
  let mut extra : Array Json := #[]
  for i in containers do
    let v := parsed.nodes[i]!
    let tag := tags[i]!
    let (payload, keys) ← match infos[i]! with
      | some (length, positions) => pure ([toString length], positions.map toString)
      | none =>
        if tag ≤ 1 then pure ([], parsed.shapes[v.key[1]!]!)
        else pure ([toString v.slots.length], (List.range v.slots.length).map toString)
    -- Defining a repeated key keeps its first position and its last value, as the runtime's
    -- property definitions do (`SerializationCollection.first_insertion_order`, `last_value`).
    -- Overwritten values are dropped before expansion, so every expanded row is reachable.
    let mut edges : List Json := []
    for (k, s) in SerializationCollection.foldMap [] (keys.zip v.slots) do
      let (t, rest) := (token s).run extra
      extra := rest
      edges := edges ++ [toJson [toJson k, t]]
    rows := rows ++ [Json.mkObj [("kind", toJson (kindText tag)), ("payload", toJson payload),
      ("edges", toJson edges)]]
  let root := ((token (.ref 0)).run extra).1
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
  -- Executes Size.lean's accounting with its charge table; accounting_eq_reachable: every
  -- charged node is reachable. Every node's children are among its slots, so table_node_count
  -- bounds the node count by the words once the table admits every node.
  let table := tableNode parsed.shapes parsed.nodes parsed.headers infos
  if !(List.range parsed.nodes.length).all fun i => decide (table i).Admitted then
    throw "charge table premise"
  let words := SerializationSize.accounting children parsed.nodes.length
    (SerializationSize.tableCharges table)
  return Json.mkObj [("ok", toJson true), ("expanded", Json.mkObj [("root", root),
    ("rows", toJson (rows ++ extra.toList))]), ("reemitted", reemitted), ("words", toJson words)]

def run (input : String) : IO Unit := do
  let requests ← IO.ofExcept (Json.parse input >>= Json.getArr?)
  let responses := requests.map fun request =>
    match evaluate request with
    | .ok result => result
    | .error error => Json.mkObj [("ok", toJson false), ("error", toJson error)]
  let output := ((Json.arr responses).compress.replace " " "\\u2028").replace " " "\\u2029"
  (← IO.getStdout).putStrLn output

end Reconcile.SerializationOracle
