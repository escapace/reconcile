import Mathlib.Data.Finmap
import Mathlib.Data.List.AList
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

/-!
# Heap model

Proof-facing definitions of the finite heaps that publication (`Heap.Publication`), immutable
reuse (`Produce.Immutable`) and the Contract oracle are stated over. The graphs of the public
functions are modeled separately, by `Spec.Graph`.

Node kinds: plain objects, arrays, dates, maps, sets, array buffers, data views and typed arrays.
The modeled surface:

- plain objects: ordered own keys, field values, prototype label
- arrays: length via list length, indexed entries with holes
- dates: millisecond timestamp
- maps: insertion-order entry sequences
- sets: insertion-order value sequences
- array buffers: byte contents
- data views: buffer ref, byte offset, byte length
- typed arrays: constructor tag, buffer ref, byte offset, length, elements
- functions: opaque atoms (never traversed)

The heap model leaves out:

- SharedArrayBuffer, proxies, accessors and property descriptors (`PropertyWrite` models
  single-key writes with descriptors and accessors)
- non-index own properties on arrays
- extra own properties on Map/Set/Date/ArrayBuffer/DataView/TypedArray
- engine-level behavior (hidden classes, GC, delete performance)
- full ECMAScript SameValue/SameValueZero proofs

Representation:

- a heap is a `Finmap` from identities to nodes
- arrays are index-only with holes (`List (Option (Value A ι))`)
- plain-object fields are an ordered list of key-value pairs (`ObjFields`), not required to have
  distinct keys; the publication theorems do not need them to
- maps and sets are ordinal sequences (`List`-based)
- buffers and views are separate node kinds
- a typed array's `elements` may hold references, which JavaScript does not allow; the theorems
  hold for any elements
- well-formedness (`NodeWF`, `HeapWF`, `RootWF`) is a separate predicate, not a subtype
-/

namespace Reconcile

/-! ## Value type -/

/-- A semantic value is either an indivisible atom or a heap reference.
    Parameterized by the atom type and the identity type. -/
inductive Value (A : Type) (ι : Type) where
  | atom : A → Value A ι
  | ref  : ι → Value A ι
deriving DecidableEq, Repr

/-! ## Property keys and prototype labels -/

/-- Abstract property key with decidable equality.
    We do not model OrdinaryOwnPropertyKeys order derivation;
    field order is taken as given. -/
structure PropertyKey where
  val : Nat
deriving DecidableEq, Hashable, Repr, Ord

/-- Abstract prototype label. -/
structure ProtoLabel where
  val : Nat
deriving DecidableEq, Repr

/-- Abstract typed-array constructor tag (e.g. Uint8Array, Float64Array). -/
structure CtorTag where
  val : Nat
deriving DecidableEq, Repr

/-! ## Object fields -/

/-- Plain-object fields as an ordered sigma list keyed by `PropertyKey`. The keys need not be
    distinct. -/
abbrev ObjFields (A : Type) (ι : Type) :=
  List (Sigma (fun _ : PropertyKey => Value A ι))

/-! ## Node payloads -/

/-- A node in the semantic heap graph. Each constructor corresponds to one
    supported kind from the specification. -/
inductive Node (A : Type) (ι : Type) where
  /-- Plain object: prototype label and ordered fields. -/
  | plainObject (proto : ProtoLabel) (fields : ObjFields A ι)
  /-- Array with holes. Index i holds `entries[i]`; `none` = hole. -/
  | array (entries : List (Option (Value A ι)))
  /-- Date with millisecond timestamp. -/
  | date (ms : Int)
  /-- Map with insertion-order entry sequence. -/
  | map (entries : List (Value A ι × Value A ι))
  /-- Set with insertion-order value sequence. -/
  | set (values : List (Value A ι))
  /-- ArrayBuffer with byte contents. -/
  | arrayBuffer (bytes : List UInt8)
  /-- DataView over a buffer. -/
  | dataView (bufferRef : ι) (byteOffset : Nat) (byteLength : Nat)
  /-- TypedArray over a buffer. Its `elements` may hold references, unlike JavaScript's. -/
  | typedArray (ctorTag : CtorTag) (bufferRef : ι) (byteOffset : Nat)
      (length : Nat) (elements : List (Value A ι))
deriving DecidableEq

/-! ## Heap -/

/-- A semantic heap: a finite map from node identifiers to nodes. -/
abbrev Heap (A : Type) (ι : Type) [DecidableEq ι] :=
  Finmap (fun _ : ι => Node A ι)

/-! ## Child references -/

/-- Collect all direct child references from a node. -/
def Node.childRefs {A : Type} {ι : Type} : Node A ι → List ι
  | .plainObject _ fields =>
    fields.filterMap fun ⟨_, v⟩ =>
      match v with | .ref r => some r | .atom _ => none
  | .array entries =>
    entries.filterMap fun
      | some (.ref r) => some r
      | _ => none
  | .date _ => []
  | .map entries =>
    entries.flatMap fun ⟨k, v⟩ =>
      (match k with | .ref r => [r] | .atom _ => []) ++
      (match v with | .ref r => [r] | .atom _ => [])
  | .set values =>
    values.filterMap fun
      | .ref r => some r
      | .atom _ => none
  | .arrayBuffer _ => []
  | .dataView bufRef _ _ => [bufRef]
  | .typedArray _ bufRef _ _ elements =>
    bufRef :: elements.filterMap fun
      | .ref r => some r
      | .atom _ => none

/-! ## Well-formedness predicates -/

/-- A node is well-formed with respect to a heap if every child reference
    is in the heap domain. -/
def NodeWF {A : Type} {ι : Type} [DecidableEq ι] (h : Heap A ι) (n : Node A ι) : Prop :=
  ∀ r ∈ n.childRefs, r ∈ h.keys

/-- A heap is well-formed when every node in it is well-formed with respect
    to the heap itself (closed under child references). -/
def HeapWF {A : Type} {ι : Type} [DecidableEq ι] (h : Heap A ι) : Prop :=
  ∀ id ∈ h.keys, ∀ node, h.lookup id = some node → NodeWF h node

/-- A root is well-formed with respect to a heap when every ref it contains
    points into the heap. -/
def RootWF {A : Type} {ι : Type} [DecidableEq ι] (h : Heap A ι) : Value A ι → Prop
  | .atom _ => True
  | .ref r  => r ∈ h.keys

end Reconcile
