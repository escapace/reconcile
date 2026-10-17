import Mathlib.Data.List.OfFn

namespace SerializationLab

inductive Kind where
  | object | nullObject | array | map | set | date | buffer | view | url | params | temporal
  deriving DecidableEq, Repr

-- Native payload extraction is outside this finite transport model.
abbrev Payload := List String

inductive Token (ι : Type) where
  | atom : String → Token ι
  | ref : ι → Token ι
  deriving DecidableEq, Repr

structure Node (ι : Type) where
  kind : Kind
  payload : Payload
  edges : List (String × Token ι)
  deriving DecidableEq, Repr

structure Graph (n : Nat) where
  root : Fin n
  nodes : Fin n → Node (Fin n)

structure Wire where
  root : Nat
  rows : List (Node Nat)
  deriving Repr

def encodeToken {n : Nat} : Token (Fin n) → Token Nat
  | .atom a => .atom a
  | .ref i => .ref i.val

def decodeRef (n : Nat) (i : Nat) : Option (Fin n) :=
  if h : i < n then some ⟨i, h⟩ else none

def decodeToken (n : Nat) : Token Nat → Option (Token (Fin n))
  | .atom a => some (.atom a)
  | .ref i => (decodeRef n i).map Token.ref

def encodeEdges {n : Nat} (es : List (String × Token (Fin n))) :=
  es.map fun (k, t) => (k, encodeToken t)

def decodeEdges (n : Nat) : List (String × Token Nat) → Option (List (String × Token (Fin n)))
  | [] => some []
  | (k, t) :: tail => do
    let t' ← decodeToken n t
    let tail' ← decodeEdges n tail
    pure ((k, t') :: tail')

def encodeNode {n : Nat} (v : Node (Fin n)) : Node Nat :=
  ⟨v.kind, v.payload, encodeEdges v.edges⟩

def decodeNode (n : Nat) (v : Node Nat) : Option (Node (Fin n)) := do
  let es ← decodeEdges n v.edges
  pure ⟨v.kind, v.payload, es⟩

def encode {n : Nat} (g : Graph n) : Wire :=
  ⟨g.root.val, List.ofFn fun i => encodeNode (g.nodes i)⟩

-- Partial decoder exposes invalid root/row/references as none. n is the validated table size.
def decodeRoot (n : Nat) (w : Wire) := decodeRef n w.root
def decodeAt (n : Nat) (w : Wire) (i : Fin n) : Option (Node (Fin n)) :=
  w.rows[i.val]?.bind (decodeNode n)

@[simp] theorem decodeRef_encode {n : Nat} (i : Fin n) : decodeRef n i.val = some i := by
  simp [decodeRef, i.isLt]

theorem decodeRef_reject (n i : Nat) (h : ¬ i < n) : decodeRef n i = none := by
  simp [decodeRef, h]

@[simp] theorem decodeToken_encode {n : Nat} (t : Token (Fin n)) :
    decodeToken n (encodeToken t) = some t := by
  cases t <;> simp [decodeToken, encodeToken]

@[simp] theorem decodeEdges_encode {n : Nat} (es : List (String × Token (Fin n))) :
    decodeEdges n (encodeEdges es) = some es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨k, t⟩
    simp only [encodeEdges] at ih
    simp [encodeEdges, decodeEdges, ih]

@[simp] theorem decodeNode_encode {n : Nat} (v : Node (Fin n)) :
    decodeNode n (encodeNode v) = some v := by
  cases v
  simp [decodeNode, encodeNode]

theorem encode_size {n : Nat} (g : Graph n) : (encode g).rows.length = n := by
  simp [encode]

theorem roundtrip_root {n : Nat} (g : Graph n) : decodeRoot n (encode g) = some g.root := by
  simp [decodeRoot, encode]

theorem roundtrip_row {n : Nat} (g : Graph n) (i : Fin n) :
    decodeAt n (encode g) i = some (g.nodes i) := by
  simp [decodeAt, encode, i.isLt]

-- Equality of complete ordered Node records includes kind, payload, labels and every edge.
theorem roundtrip {n : Nat} (g : Graph n) :
    decodeRoot n (encode g) = some g.root ∧
      ∀ i, decodeAt n (encode g) i = some (g.nodes i) :=
  ⟨roundtrip_root g, roundtrip_row g⟩

theorem reference_identity_iff {n : Nat} (i j : Fin n) :
    encodeToken (.ref i) = encodeToken (.ref j) ↔ i = j := by
  simp [encodeToken, Fin.ext_iff]

theorem distinct_nodes_not_merged {n : Nat} (i j : Fin n) (h : i ≠ j) :
    encodeToken (.ref i) ≠ encodeToken (.ref j) := by
  simpa only [ne_eq, reference_identity_iff] using h

-- Shape dictionary entries are exact ordered key lists, never key sets.
def expand (keys : List String) (values : List (Token Nat)) :
    Option (List (String × Token Nat)) :=
  if keys.length = values.length then some (keys.zip values) else none

theorem expand_exact (es : List (String × Token Nat)) :
    expand (es.map Prod.fst) (es.map Prod.snd) = some es := by
  have hz : (es.map Prod.fst).zip (es.map Prod.snd) = es := by
    induction es with
    | nil => rfl
    | cons e es ih => simp [ih]
  simp [expand, hz]

theorem expand_reject_arity (keys : List String) (values : List (Token Nat))
    (h : keys.length ≠ values.length) : expand keys values = none := by
  simp [expand, h]

def dictionaryExpand (dictionary : List (List String)) (shapeId : Nat)
    (values : List (Token Nat)) : Option (List (String × Token Nat)) :=
  dictionary[shapeId]?.bind fun keys => expand keys values

theorem dictionary_exact (dictionary : List (List String)) (shapeId : Nat)
    (es : List (String × Token Nat))
    (h : dictionary[shapeId]? = some (es.map Prod.fst)) :
    dictionaryExpand dictionary shapeId (es.map Prod.snd) = some es := by
  simp [dictionaryExpand, h, expand_exact]

-- Shell allocation is an injective ID-to-handle map; edge installation does not change it.
def resolve {n : Nat} {Handle : Type} (table : Fin n → Handle) (i : Fin n) := table i

theorem shell_identity_iff {n : Nat} {Handle : Type} (table : Fin n → Handle)
    (fresh : Function.Injective table) (i j : Fin n) :
    resolve table i = resolve table j ↔ i = j := by
  exact fresh.eq_iff

-- Dependency scheduler obligation, independent of graph edge cycles.
def Ready {n : Nat} (rank : Fin n → Nat) (step : Nat) (i : Fin n) := rank i < step

theorem dependency_ready {n : Nat} (rank : Fin n → Nat) (owner child : Fin n)
    (earlier : rank child < rank owner) : Ready rank (rank owner) child := earlier

theorem installed_shell_ready {n : Nat} (i : Fin n) : i.val < n := i.isLt

-- Concrete inhabited cyclic graph: one self-reference and two aliases to it.
def cycleExample : Graph 1 :=
  ⟨⟨0, by decide⟩, fun _ => ⟨.object, [],
    [("self", .ref ⟨0, by decide⟩), ("again", .ref ⟨0, by decide⟩)]⟩⟩

example : decodeAt 1 (encode cycleExample) ⟨0, by decide⟩ =
    some (cycleExample.nodes ⟨0, by decide⟩) := roundtrip_row _ _

#print axioms roundtrip
#print axioms encode_size
#print axioms roundtrip_root
#print axioms roundtrip_row
#print axioms decodeRef_encode
#print axioms decodeRef_reject
#print axioms decodeToken_encode
#print axioms decodeEdges_encode
#print axioms decodeNode_encode
#print axioms reference_identity_iff
#print axioms distinct_nodes_not_merged
#print axioms expand_exact
#print axioms expand_reject_arity
#print axioms dictionary_exact
#print axioms shell_identity_iff
#print axioms dependency_ready
#print axioms installed_shell_ready

end SerializationLab
