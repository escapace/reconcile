import Serialization.Reconstruction
import Lean

open Lean SerializationLab SerializationV9

namespace Reconcile.SerializationOracle

abbrev E := Except String

def need {α : Type} (message : String) : Option α → E α
  | some a => .ok a
  | none => .error message

def nat (j : Json) : E Nat := fromJson? j
def integer (j : Json) : E Int := fromJson? j
def strings (j : Json) : E (List String) := do
  (← j.getArr?).toList.mapM Json.getStr?

def token (j : Json) : E (Token Nat) := do
  match j with
  | .null | .bool _ | .str _ => return .atom j.compress
  | .num q =>
    if q.mantissa < 0 then
      let i ← integer j
      return .ref (-i - 1).toNat
    return .atom j.compress
  | .arr a =>
    if a.size == 1 then
      let i ← integer a[0]!
      if i < 0 && i ≥ -5 then return .atom j.compress
      throw "invalid atom tag"
    if a.size == 2 then
      let tag ← integer a[0]!
      if tag == -7 then
        match a[1]! with
        | .num q =>
          if q.mantissa < 0 then return .atom a[1]!.compress
          throw "escaped number must be negative"
        | _ => throw "escaped number required"
      if tag != -6 then throw "invalid bigint tag"
      let text ← a[1]!.getStr?
      let value ← need "invalid bigint" text.toInt?
      if toString value != text then throw "noncanonical bigint"
      return .atom j.compress
    throw "invalid token arity"
  | _ => throw "object token unsupported"

def modelToken (t : Token Nat) : Json := match t with
  | .atom a => toJson ([toJson (0 : Nat), toJson a] : List Json)
  | .ref i => toJson ([toJson (1 : Nat), toJson i] : List Json)

def wireToken (t : Token Nat) : E Json := match t with
  | .atom a => do
    let j ← Json.parse a
    match j with
    | .num q => if q.mantissa < 0 then return toJson [toJson (-7 : Int), j] else return j
    | _ => return j
  | .ref i => pure (toJson (-((i : Int) + 1)))

def kindText : Kind → String
  | .object => "object"
  | .nullObject => "nullObject"
  | .array => "array"
  | _ => "unsupported"

def modelNode (v : Node Nat) : Json := Json.mkObj [
  ("kind", toJson (kindText v.kind)), ("payload", toJson v.payload),
  ("edges", toJson (v.edges.map fun (key, t) => toJson [toJson key, modelToken t]))]

def parseRow (shapes : List (List String)) (j : Json) : E (Node Nat) := do
  let a ← j.getArr?
  if a.size < 2 then throw "row arity"
  let tag ← nat a[0]!
  let header ← nat a[1]!
  let rest := (a.toList.drop 2)
  if tag == 0 || tag == 1 then
    let values ← rest.mapM token
    -- Executes the frozen finite shape dictionary expansion, including arity rejection.
    let es ← need "shape missing or wrong arity" (dictionaryExpand shapes header values)
    return ⟨if tag == 0 then .object else .nullObject, [], es⟩
  if tag == 2 then
    if header > 4294967295 then throw "native array length"
    if rest.length != header then throw "dense array arity"
    let values ← rest.mapM token
    return ⟨.array, [toString header], values.zipIdx |>.map (fun (t, i) => (toString i, t))⟩
  if tag == 3 then
    if header > 4294967295 then throw "native array length"
    if rest.length % 2 != 0 then throw "sparse array arity"
    let mut es := []
    let mut previous : Option Nat := none
    for p in [:rest.length / 2] do
      let k ← nat rest[p * 2]!
      if k ≥ header then throw "sparse index out of bounds"
      if previous.any (fun old => k ≤ old) then throw "sparse indices not increasing"
      let t ← token rest[p * 2 + 1]!
      es := es ++ [(toString k, t)]
      previous := some k
    let pairs ← es.mapM fun (key, t) => do
      let i ← need "sparse key" key.toNat?
      pure (i, t)
    let installed ← need "sparse write rejected"
      (SerializationV9.fill (allocatedSparse header) pairs)
    if installed.length != header then throw "sparse length mismatch"
    for (i, t) in pairs do
      if installed.slot i != some t then throw "sparse presence mismatch"
    return ⟨.array, [toString header], es⟩
  throw "unsupported native row kind"

def reemit (root : Token Nat) (rows : List (Node Nat)) : E Json := do
  let mut shapes : List (List String) := []
  let mut output : List Json := []
  for row in rows do
    if row.kind == .object || row.kind == .nullObject then
      let sid := shapes.length
      shapes := shapes ++ [row.edges.map Prod.fst]
      let values ← row.edges.mapM fun (_, t) => wireToken t
      output := output ++ [toJson ([toJson (if row.kind == .object then 0 else 1 : Nat), toJson sid] ++ values)]
    else if row.kind == .array then
      let length ← need "missing array length" row.payload.head?
      let length ← need "invalid array length" length.toNat?
      let mut values := [toJson (3 : Nat), toJson length]
      for (key, t) in row.edges do
        let i ← need "invalid array index" key.toNat?
        values := values ++ [toJson i, ← wireToken t]
      output := output ++ [toJson values]
    else throw "unsupported model kind"
  return toJson [← wireToken root, toJson shapes, toJson output]

def evaluate (request : Json) : E Json := do
  let doc ← (← request.getObjVal? "wire").getArr?
  if doc.size != 3 then throw "envelope arity"
  let shapeJson ← doc[1]!.getArr?
  let rawRows ← doc[2]!.getArr?
  let mut shapes : List (List String) := List.replicate shapeJson.size []
  let mut checked : List Nat := []
  let mut rows := []
  for raw in rawRows do
    let fields ← raw.getArr?
    if fields.size < 2 then throw "row arity"
    let kind ← nat fields[0]!
    if kind == 0 || kind == 1 then
      let sid ← nat fields[1]!
      if sid ∉ checked then
        let selected ← need "shape missing" shapeJson[sid]?
        let keys ← strings selected
        shapes := shapes.set sid keys
        -- Execute proved first-use shape check; never interpret unused dictionary entries.
        if !(shapeCheck shapes checked sid) then throw "duplicate shape key"
        checked := sid :: checked
    let row ← parseRow shapes raw
    rows := rows ++ [row]
  let root ← token doc[0]!
  let n := rows.length
  -- Executes the original decoder at every token/row, then original encoder.
  let typedRoot ← need "root reference out of range" (decodeToken n root)
  let typedRows ← rows.mapM fun row => need "row reference out of range" (decodeNode n row)
  let roundRoot := encodeToken typedRoot
  let roundRows := typedRows.map encodeNode
  let expanded := Json.mkObj [("root", modelToken root), ("rows", toJson (rows.map modelNode))]
  let roundtrip := Json.mkObj [("root", modelToken roundRoot), ("rows", toJson (roundRows.map modelNode))]
  let emitted ← reemit roundRoot roundRows
  return Json.mkObj [("ok", toJson true), ("expanded", expanded), ("roundtrip", roundtrip),
    ("wireFromModel", emitted), ("root", modelToken root), ("rows", toJson (rows.map modelNode)),
    ("reemitted", emitted)]

def run (input : String) : IO Unit := do
  let requests ← IO.ofExcept (Json.parse input >>= Json.getArr?)
  let responses := requests.map fun request =>
    match evaluate request with
    | .ok result => result
    | .error error => Json.mkObj [("ok", toJson false), ("error", toJson error)]
  let output := ((Json.arr responses).compress.replace "\u2028" "\\u2028").replace "\u2029" "\\u2029"
  (← IO.getStdout).putStrLn output

end Reconcile.SerializationOracle
