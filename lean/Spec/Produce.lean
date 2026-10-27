import Spec.Graph

/-!
# `produce` and `snapshot`: the reference models

`produce(current, recipe)` runs the recipe on drafts and returns the result with every object the
recipe left unchanged kept as the original. The reference takes the recipe as a list of
operations on a *draft heap*: the current nodes, which the operations change in place as their
drafts record them, and the objects the recipe creates, appended after them. An operation a draft
refuses (a read-only or non-configurable property, a non-extensible object) is not generated, nor
is an assignment to an own accessor, which runs its setter on the draft and which the model leaves
out.

Finalization keeps a current node when its subtree is unchanged: its own contents equal the
original's and every node it references is itself unchanged (the greatest such set). Every other
current node becomes a new object with the draft's contents; a changed object keeps its
prototype, its extensibility and the attributes of its existing data properties, an added
property is writable, enumerable and configurable, and an accessor becomes a data property with
the getter's value and enumerability. An object the recipe created is kept as itself unless it
holds a draft, in which case it is copied. A draft reads a `Date`, buffer or view as a copy, which
is the result's value only when it differs from the original; a view's copy differs when its
buffer's does.

`snapshot(value)` copies every node with `Obj.copy`, the rule by which `reconcile` adds a node:
data properties writable and configurable with their enumerability, accessors as data, prototypes
kept.
-/

namespace Reconcile.Spec.Produce

open Reconcile.Spec

/-- One recipe operation on the draft of a node, or the creation of an object. -/
inductive Op where
  | setKey (node : Nat) (key : String) (value : Val)
  | deleteKey (node : Nat) (key : String)
  | setIndex (node : Nat) (index : Nat) (value : Val)
  | setLength (node : Nat) (length : Nat)
  | mapSet (node : Nat) (key value : Val)
  | mapDelete (node : Nat) (key : Val)
  | setAdd (node : Nat) (value : Val)
  | setDelete (node : Nat) (value : Val)
  | setTime (node : Nat) (ms : Int)
  /-- Writes one byte of a buffer. -/
  | setByte (node : Nat) (index byte : Nat)
  | create (obj : Obj)
  deriving Repr

structure Input where
  cur : Graph
  ops : List Op
  /-- What the recipe returns: a reference to a draft or a created object, or a primitive. -/
  returns : Val
  /-- Whether the recipe returns `current` itself, which discards its changes. -/
  returnsCurrent : Bool

/-- An array with `length` entries: truncated, or extended with holes. -/
def resize (entries : List (Option Val)) (length : Nat) : List (Option Val) :=
  if length ≤ entries.length then entries.take length
  else entries ++ List.replicate (length - entries.length) none

/-- Applies one operation to the draft heap; `none` when a draft refuses it, and for an
assignment to an own accessor, which the model leaves out. -/
def apply (heap : Array Obj) : Op → Option (Array Obj)
  | .setKey node key value =>
    match heap[node]? with
    | some (.object proto fields extensible) =>
      match fields.lookup key with
      | some (.data _ a) =>
        if a.writable then
          some (heap.setIfInBounds node (.object proto (fields.map fun (k, s) =>
            if k = key then (k, .data value a) else (k, s)) extensible))
        else none
      | some (.accessor ..) => none
      | none =>
        if extensible then
          some (heap.setIfInBounds node (.object proto (fields ++ [(key, .data value .plain)])
            extensible))
        else none
    | _ => none
  | .deleteKey node key =>
    match heap[node]? with
    | some (.object proto fields extensible) =>
      match fields.lookup key with
      | some s =>
        if s.configurable then
          some (heap.setIfInBounds node (.object proto (fields.filter fun (k, _) => k != key)
            extensible))
        else none
      | none => some heap
    | _ => none
  | .setIndex node index value =>
    match heap[node]? with
    | some (.array entries ext) =>
      let present := (entries[index]?.bind id).isSome
      if ext = .frozen then none
      else if !present && ext != .extensible then none
      else
        let grown := resize entries (max entries.length (index + 1))
        some (heap.setIfInBounds node (.array (grown.zipIdx.map fun (e, i) =>
          if i = index then some value else e) ext))
    | _ => none
  | .setLength node length =>
    match heap[node]? with
    | some (.array entries ext) =>
      if ext = .frozen then none
      else if ext = .sealed && (entries.drop length).any Option.isSome then none
      else some (heap.setIfInBounds node (.array (resize entries length) ext))
    | _ => none
  | .mapSet node key value =>
    match heap[node]? with
    | some (.map entries) =>
      let replaced := entries.map fun (k, v) => if k = key then (k, value) else (k, v)
      some (heap.setIfInBounds node
        (.map (if entries.any (·.1 = key) then replaced else entries ++ [(key, value)])))
    | _ => none
  | .mapDelete node key =>
    match heap[node]? with
    | some (.map entries) => some (heap.setIfInBounds node (.map (entries.filter (·.1 != key))))
    | _ => none
  | .setAdd node value =>
    match heap[node]? with
    | some (.set members) =>
      some (heap.setIfInBounds node
        (.set (if members.contains value then members else members ++ [value])))
    | _ => none
  | .setDelete node value =>
    match heap[node]? with
    | some (.set members) =>
      some (heap.setIfInBounds node (.set (members.filter (· != value))))
    | _ => none
  | .setTime node ms =>
    match heap[node]? with
    | some (.date _) => some (heap.setIfInBounds node (.date ms))
    | _ => none
  | .setByte node index byte =>
    match heap[node]? with
    | some (.buffer bytes max) =>
      if index < bytes.length then some (heap.setIfInBounds node (.buffer (bytes.set index byte) max))
      else none
    | _ => none
  | .create obj => some (heap.push obj)

/-- Applies the recipe; `none` when an operation is refused. -/
def applyAll (heap : Array Obj) : List Op → Option (Array Obj)
  | [] => some heap
  | op :: rest => (apply heap op).bind fun heap => applyAll heap rest

/-- Whether draft heap node `r` is a current `Date` or buffer the recipe changed, or a current view
whose buffer it changed: the copy the recipe holds is the result's value, so a created object may
hold it. -/
def changedCopy (cur : Graph) (heap : Array Obj) (r : Nat) : Bool :=
  let changed (i : Nat) : Bool := i < cur.nodes.size && heap[i]? != some (cur.node i)
  match cur.node r with
  | .date _ | .buffer .. => changed r
  | .view _ storage _ _ =>
    changed r ||
      match storage with
      | .ref b => changed b
      | .prim _ => false
  | _ => false

/-- Whether created node `i` may keep reference `r` and stay itself: a kept created object, or a
changed copy. A current object the recipe holds is a draft, which the result unwraps. -/
def createdKeeps (cur : Graph) (heap : Array Obj) (set : List Nat) (r : Nat) : Bool :=
  (cur.nodes.size ≤ r && set.contains r) || (r < cur.nodes.size && changedCopy cur heap r)

/-- The nodes the result keeps as themselves: the greatest set in which every current node equals
its draft and refers only to nodes of the set, and every created object refers only to kept
created objects and changed copies. -/
def kept (cur : Graph) (heap : Array Obj) : List Nat :=
  let n := cur.nodes.size
  let start := (List.range heap.size).filter fun i => i < n → heap[i]? = some (cur.node i)
  go heap.size start
where
  go : Nat → List Nat → List Nat
    | 0, set => set
    | fuel + 1, set =>
      let pruned := set.filter fun i =>
        (heap[i]?.getD default).refs.all fun r =>
          if i < cur.nodes.size then set.contains r else createdKeeps cur heap set r
      if pruned.length = set.length then set else go fuel pruned

/-- A changed current object rebuilt from its draft: prototype, extensibility and existing data
attributes kept, accessors as data with the getter's value and enumerability; a changed array
keeps only whether it is extensible. -/
def rebuild : Obj → Obj
  | .object proto fields extensible =>
    .object proto (fields.map fun (k, s) =>
      match s with
      | .data v a => (k, .data v a)
      | .accessor v _ e _ => (k, .data v (.copied e))) extensible
  | .array entries ext =>
    normalizeObj (.array entries (if ext = .extensible then .extensible else .nonExtensible))
  | o => o

/-- The origin of a result node: a kept current node, a kept object the recipe created, or none
for a new object. -/
inductive Origin where
  | cur (id : Nat)
  | new (id : Nat)
  | fresh
  deriving DecidableEq, Repr

def Origin.toJson : Origin → Lean.Json
  | .cur id => Lean.toJson id
  | .new id => Lean.toJson (-(Int.ofNat id) - 1)
  | .fresh => .null

instance : Lean.ToJson Origin := ⟨Origin.toJson⟩

structure Outcome where
  ok : Bool
  origins : Array Origin
  nodes : Array Obj
  root : Val
  deriving Lean.ToJson, Repr

/-- Runs the reference. The result's node ids are the draft heap's. -/
def run (raw : Input) : Outcome :=
  let cur := raw.cur.normalize
  let n := cur.nodes.size
  match applyAll cur.nodes raw.ops with
  | none => { ok := false, origins := #[], nodes := #[], root := .prim .undef }
  | some heap =>
    if raw.returnsCurrent then
      { ok := true, origins := (Array.range n).map Origin.cur, nodes := cur.nodes,
        root := cur.root }
    else
      let kept := kept cur heap
      let origins := (Array.range heap.size).map fun i =>
        if !kept.contains i then .fresh else if i < n then .cur i else .new (i - n)
      let nodes := (Array.range heap.size).map fun i =>
        if kept.contains i then heap[i]?.getD default else rebuild (heap[i]?.getD default)
      { ok := true, origins, nodes, root := raw.returns }

/-- `snapshot`: every node copied. -/
def snapshot (cur : Graph) : Outcome :=
  { ok := true, origins := cur.nodes.map fun _ => .fresh, nodes := cur.nodes.map Obj.copy,
    root := cur.root }

/-! ## JSON for operations -/

open Lean in
def Op.fromJson (j : Json) : Except String Op := do
  let op ← (← j.getObjVal? "op").getStr?
  let node := (j.getObjVal? "node" >>= fromJson?) |>.toOption.getD (0 : Nat)
  match op with
  | "setKey" => pure (.setKey node (← (← j.getObjVal? "key").getStr?)
      (← fromJson? (← j.getObjVal? "value")))
  | "deleteKey" => pure (.deleteKey node (← (← j.getObjVal? "key").getStr?))
  | "setIndex" => pure (.setIndex node (← fromJson? (← j.getObjVal? "index"))
      (← fromJson? (← j.getObjVal? "value")))
  | "setLength" => pure (.setLength node (← fromJson? (← j.getObjVal? "length")))
  | "mapSet" => pure (.mapSet node (← fromJson? (← j.getObjVal? "key"))
      (← fromJson? (← j.getObjVal? "value")))
  | "mapDelete" => pure (.mapDelete node (← fromJson? (← j.getObjVal? "key")))
  | "setAdd" => pure (.setAdd node (← fromJson? (← j.getObjVal? "value")))
  | "setDelete" => pure (.setDelete node (← fromJson? (← j.getObjVal? "value")))
  | "setTime" => pure (.setTime node (← fromJson? (← j.getObjVal? "ms")))
  | "setByte" => pure (.setByte node (← fromJson? (← j.getObjVal? "index"))
      (← fromJson? (← j.getObjVal? "byte")))
  | "create" => pure (.create (← fromJson? (← j.getObjVal? "obj")))
  | other => throw s!"unknown op {other}"

instance : Lean.FromJson Op := ⟨Op.fromJson⟩

end Reconcile.Spec.Produce
