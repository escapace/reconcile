import Lean

/-!
# Specification graphs

The executable heap model that the end-to-end specifications of `reconcile`, `produce` and
`snapshot` are stated over and that the random differential bridges exchange with the runtime as
JSON. Unlike `Heap/Defs.lean`, which is proof-facing, every definition here computes.

A graph has numbered nodes and a root value. A plain object carries its prototype label, its own
keys in order, each with a data slot (value and attributes) or an accessor slot (the value its
getter returns and whether it has a setter that stores, a setter that drops, or no setter), and
its extensibility. An array carries its entries with holes and an extensibility level. Maps and
sets carry their entries in insertion order; a date its time. Primitives include an `atom`, an
object kept by reference, such as a function, identified by a label.

Outside the model: prototypes with accessors, symbol keys, array index keys on objects, `-0`
and `NaN`, buffers, views, URLs and Temporal values.
-/

namespace Reconcile.Spec

open Lean

/-- A primitive, or an object kept by reference identified by a label. -/
inductive Prim where
  | undef
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | atom (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A slot value: a primitive or a reference to a node of the same graph. -/
inductive Val where
  | prim (p : Prim)
  | ref (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The attributes of a data property. -/
structure Attrs where
  writable : Bool
  enumerable : Bool
  configurable : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The attributes an assignment gives a new property. -/
def Attrs.plain : Attrs := ⟨true, true, true⟩

/-- An own property: data with attributes, or an accessor whose getter returns `value` and whose
setter is absent (`none`), stores what it receives (`some true`) or drops it (`some false`). -/
inductive Slot where
  | data (value : Val) (attrs : Attrs)
  | accessor (value : Val) (setter : Option Bool) (enumerable configurable : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- The value a read of the slot returns. -/
def Slot.value : Slot → Val
  | .data v _ => v
  | .accessor v _ _ _ => v

def Slot.enumerable : Slot → Bool
  | .data _ a => a.enumerable
  | .accessor _ _ e _ => e

def Slot.configurable : Slot → Bool
  | .data _ a => a.configurable
  | .accessor _ _ _ c => c

/-- A prototype label: `Object.prototype`, `null`, or the prototype of class `id`. -/
inductive Proto where
  | object
  | null
  | cls (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- An array's extensibility level. -/
inductive Ext where
  | extensible
  | nonExtensible
  | sealed
  | frozen
  deriving DecidableEq, Repr, Inhabited

/-- A node. -/
inductive Obj where
  | object (proto : Proto) (fields : List (String × Slot)) (extensible : Bool)
  | array (entries : List (Option Val)) (ext : Ext)
  | map (entries : List (Val × Val))
  | set (members : List Val)
  | date (ms : Int)
  deriving DecidableEq, Repr, Inhabited

inductive Kind where
  | object
  | array
  | map
  | set
  | date
  deriving DecidableEq, Repr, Inhabited

def Obj.kind : Obj → Kind
  | .object .. => .object
  | .array .. => .array
  | .map .. => .map
  | .set .. => .set
  | .date .. => .date

/-- The references a node holds, in traversal order: object slot values in key order, array
entries in index order, map keys and values entry by entry, set members. -/
def Obj.refs : Obj → List Nat
  | .object _ fields _ => fields.filterMap fun (_, slot) =>
      match slot.value with
      | .ref id => some id
      | .prim _ => none
  | .array entries _ => entries.filterMap fun
      | some (.ref id) => some id
      | _ => none
  | .map entries => entries.flatMap fun (k, v) =>
      (match k with | .ref id => [id] | .prim _ => []) ++
      (match v with | .ref id => [id] | .prim _ => [])
  | .set members => members.filterMap fun
      | .ref id => some id
      | .prim _ => none
  | .date _ => []

/-- A graph: nodes by id and a root value. -/
structure Graph where
  nodes : Array Obj
  root : Val
  deriving DecidableEq, Repr, Inhabited

def Graph.node (g : Graph) (id : Nat) : Obj := g.nodes[id]?.getD default

/-- Whether every reference points into the graph. -/
def Graph.closed (g : Graph) : Bool :=
  (match g.root with | .ref id => id < g.nodes.size | .prim _ => true) &&
    g.nodes.all fun node => node.refs.all (· < g.nodes.size)

/-! ## JSON

The wire form the bridges use. A value is `null`, a boolean, a number, a string, `{"undef":true}`,
`{"atom":n}` or `{"ref":n}`. A data slot is `{"v":value,"a":[writable,enumerable,configurable]}`,
an accessor `{"get":value,"set":null|true|false,"e":bool,"c":bool}`. A node carries `"kind"`;
an object `"proto"` (`"object"`, `"null"` or `{"cls":n}`), `"fields"` as `[key, slot]` pairs and
`"extensible"`; an array `"entries"` with `{"hole":true}` for a hole and `"ext"`; a map
`"entries"` as `[key, value]` pairs; a set `"members"`; a date `"ms"`. A graph is
`{"nodes":[...],"root":value}`. -/

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

private def flag (j : Json) (key : String) : Except String Bool := do fromJson? (← field j key)

def Val.fromJson : Json → Except String Val
  | .null => pure (.prim .null)
  | .bool b => pure (.prim (.bool b))
  | .str s => pure (.prim (.str s))
  | j@(.num _) => do pure (.prim (.num (← fromJson? j)))
  | j@(.obj _) =>
    match field j "ref" with
    | .ok r => do pure (.ref (← fromJson? r))
    | .error _ =>
      match field j "atom" with
      | .ok a => do pure (.prim (.atom (← fromJson? a)))
      | .error _ =>
        match field j "undef" with
        | .ok _ => pure (.prim .undef)
        | .error _ => throw "invalid value"
  | _ => throw "invalid value"

def Val.toJson : Val → Json
  | .prim .undef => Json.mkObj [("undef", true)]
  | .prim .null => .null
  | .prim (.bool b) => .bool b
  | .prim (.num n) => Lean.toJson n
  | .prim (.str s) => .str s
  | .prim (.atom id) => Json.mkObj [("atom", Lean.toJson id)]
  | .ref id => Json.mkObj [("ref", Lean.toJson id)]

instance : FromJson Val := ⟨Val.fromJson⟩
instance : ToJson Val := ⟨Val.toJson⟩

def Attrs.fromJson (j : Json) : Except String Attrs := do
  match (← j.getArr?).toList with
  | [w, e, c] => pure ⟨← fromJson? w, ← fromJson? e, ← fromJson? c⟩
  | _ => throw "invalid attributes"

def Attrs.toJson (a : Attrs) : Json :=
  Json.arr #[.bool a.writable, .bool a.enumerable, .bool a.configurable]

instance : FromJson Attrs := ⟨Attrs.fromJson⟩
instance : ToJson Attrs := ⟨Attrs.toJson⟩

def Slot.fromJson (j : Json) : Except String Slot :=
  match field j "v" with
  | .ok v => do pure (.data (← fromJson? v) (← fromJson? (← field j "a")))
  | .error _ => do
    let value ← fromJson? (← field j "get")
    let setter ← match ← field j "set" with
      | .null => pure none
      | .bool b => pure (some b)
      | _ => throw "invalid setter"
    pure (.accessor value setter (← flag j "e") (← flag j "c"))

def Slot.toJson : Slot → Json
  | .data v a => Json.mkObj [("v", Lean.toJson v), ("a", Lean.toJson a)]
  | .accessor v setter e c =>
    Json.mkObj [("get", Lean.toJson v),
      ("set", match setter with | none => .null | some b => .bool b),
      ("e", .bool e), ("c", .bool c)]

instance : FromJson Slot := ⟨Slot.fromJson⟩
instance : ToJson Slot := ⟨Slot.toJson⟩

def Proto.fromJson : Json → Except String Proto
  | .str "object" => pure .object
  | .str "null" => pure .null
  | j@(.obj _) => do pure (.cls (← fromJson? (← field j "cls")))
  | _ => throw "invalid prototype"

def Proto.toJson : Proto → Json
  | .object => .str "object"
  | .null => .str "null"
  | .cls id => Json.mkObj [("cls", Lean.toJson id)]

instance : FromJson Proto := ⟨Proto.fromJson⟩
instance : ToJson Proto := ⟨Proto.toJson⟩

def Ext.fromJson : Json → Except String Ext
  | .str "extensible" => pure .extensible
  | .str "nonExtensible" => pure .nonExtensible
  | .str "sealed" => pure .sealed
  | .str "frozen" => pure .frozen
  | _ => throw "invalid extensibility"

def Ext.toJson : Ext → Json
  | .extensible => .str "extensible"
  | .nonExtensible => .str "nonExtensible"
  | .sealed => .str "sealed"
  | .frozen => .str "frozen"

instance : FromJson Ext := ⟨Ext.fromJson⟩
instance : ToJson Ext := ⟨Ext.toJson⟩

private def pair (j : Json) : Except String (Json × Json) := do
  match (← j.getArr?).toList with
  | [a, b] => pure (a, b)
  | _ => throw "invalid pair"

private def entry (j : Json) : Except String (Option Val) :=
  match j with
  | .obj _ =>
    match field j "hole" with
    | .ok _ => pure none
    | .error _ => do pure (some (← fromJson? j))
  | _ => do pure (some (← fromJson? j))

def Obj.fromJson (j : Json) : Except String Obj := do
  match ← field j "kind" with
  | .str "object" =>
    let fields ← (← (← field j "fields").getArr?).toList.mapM fun f => do
      let (k, s) ← pair f
      let slot : Slot ← fromJson? s
      pure ((← k.getStr?), slot)
    pure (.object (← fromJson? (← field j "proto")) fields (← flag j "extensible"))
  | .str "array" =>
    let entries ← (← (← field j "entries").getArr?).toList.mapM entry
    pure (.array entries (← fromJson? (← field j "ext")))
  | .str "map" =>
    let entries ← (← (← field j "entries").getArr?).toList.mapM fun e => do
      let (k, v) ← pair e
      let key : Val ← fromJson? k
      let value : Val ← fromJson? v
      pure (key, value)
    pure (.map entries)
  | .str "set" =>
    pure (.set (← (← (← field j "members").getArr?).toList.mapM fromJson?))
  | .str "date" => do pure (.date (← fromJson? (← field j "ms")))
  | _ => throw "invalid kind"

def Obj.toJson : Obj → Json
  | .object proto fields extensible =>
    Json.mkObj [("kind", .str "object"), ("proto", Lean.toJson proto),
      ("fields", Json.arr (fields.map fun (k, s) => Json.arr #[.str k, Lean.toJson s]).toArray),
      ("extensible", .bool extensible)]
  | .array entries ext =>
    Json.mkObj [("kind", .str "array"),
      ("entries", Json.arr (entries.map fun
        | none => Json.mkObj [("hole", true)]
        | some v => Lean.toJson v).toArray),
      ("ext", Lean.toJson ext)]
  | .map entries =>
    Json.mkObj [("kind", .str "map"),
      ("entries", Json.arr (entries.map fun (k, v) =>
        Json.arr #[Lean.toJson k, Lean.toJson v]).toArray)]
  | .set members =>
    Json.mkObj [("kind", .str "set"), ("members", Json.arr (members.map Lean.toJson).toArray)]
  | .date ms => Json.mkObj [("kind", .str "date"), ("ms", Lean.toJson ms)]

instance : FromJson Obj := ⟨Obj.fromJson⟩
instance : ToJson Obj := ⟨Obj.toJson⟩

def Graph.fromJson (j : Json) : Except String Graph := do
  let nodes ← (← (← field j "nodes").getArr?).mapM fromJson?
  pure ⟨nodes, ← fromJson? (← field j "root")⟩

def Graph.toJson (g : Graph) : Json :=
  Json.mkObj [("nodes", Json.arr (g.nodes.map Lean.toJson)), ("root", Lean.toJson g.root)]

instance : FromJson Graph := ⟨Graph.fromJson⟩
instance : ToJson Graph := ⟨Graph.toJson⟩

/-- An array's extensibility level as the integrity test observes it: a non-extensible array with
no element has no configurable property, so it reads as sealed. -/
def observedExt (entries : List (Option Val)) : Ext → Ext
  | .nonExtensible => if entries.any Option.isSome then .nonExtensible else .sealed
  | ext => ext

/-- A node with its array extensibility as observed. -/
def normalizeObj : Obj → Obj
  | .array entries ext => .array entries (observedExt entries ext)
  | o => o

/-- A graph with every node as observed. -/
def Graph.normalize (g : Graph) : Graph :=
  { g with nodes := g.nodes.map normalizeObj }

end Reconcile.Spec
