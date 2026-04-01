/-
  Reconcile semantic core — proof-friendly definitions.

  Formal scope (frozen):
    Supported node kinds:
      PlainObject, Array, Date, Map, Set, ArrayBuffer, DataView, TypedArray.
    Supported surface:
      - plain objects: ordered own keys, field values, prototype label
      - arrays: length via list length, indexed entries with holes
      - dates: millisecond timestamp
      - maps: insertion-order entry sequences
      - sets: insertion-order value sequences
      - array buffers: byte contents
      - data views: buffer ref, byte offset, byte length
      - typed arrays: constructor tag, buffer ref, byte offset, length, elements
      - functions: opaque atoms (never traversed)

    Excluded (will not be reopened):
      - SharedArrayBuffer, proxies, accessors, descriptors
      - non-index own properties on arrays
      - extra own properties on Map/Set/Date/ArrayBuffer/DataView/TypedArray
      - engine-level behavior (hidden classes, GC, delete perf)
      - full ECMAScript SameValue/SameValueZero proofs
      - custom snapshot/reconcile implementations

  Design decisions:
    - arrays are index-only with holes (List (Option (Value A ι)))
    - plain objects are ordered exact-key records (AList)
    - maps and sets are ordinal sequences (List-based)
    - buffers and views are separate node kinds
    - no descriptors/proxies/SharedArrayBuffer
    - Finmap for heaps and witness maps
    - AList for ordered plain-object fields
    - Relation.ReflTransGen for reachability
    - subtypes used sparingly; prefer separate WF predicates

  This module is completely separate from the existing EFSM proof tree.
-/

import Mathlib.Data.Finmap
import Mathlib.Data.List.AList
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

namespace Reconcile

/-! ## Identity types -/

/-- Current-heap node identifier. -/
structure CurId where
  val : Nat
deriving DecidableEq, Hashable, Repr, Ord

/-- Next-heap node identifier. -/
structure NextId where
  val : Nat
deriving DecidableEq, Hashable, Repr, Ord

/-- Fresh node identifier allocated during reconcile. -/
structure FreshId where
  val : Nat
deriving DecidableEq, Hashable, Repr, Ord

/-- Result-heap node identifier: either a reused current node or a freshly allocated one. -/
abbrev ResId := CurId ⊕ FreshId

instance : DecidableEq ResId := inferInstance

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

/-! ## Object fields (ordered, duplicate-free) -/

/-- Plain-object fields as an ordered sigma list keyed by PropertyKey.
    NodupKeys is enforced by a separate WF predicate, not a subtype,
    following the plan's guidance to use subtypes sparingly. -/
abbrev ObjFields (A : Type) (ι : Type) :=
  List (Sigma (fun _ : PropertyKey => Value A ι))

/-! ## Node payloads -/

/-- A node in the semantic heap graph. Each constructor corresponds to one
    supported kind from the specification. -/
inductive Node (A : Type) (ι : Type) where
  /-- Plain object: prototype label, ordered fields (raw list;
      NodupKeys is a separate WF condition). -/
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
  /-- TypedArray over a buffer. -/
  | typedArray (ctorTag : CtorTag) (bufferRef : ι) (byteOffset : Nat)
      (length : Nat) (elements : List (Value A ι))
deriving DecidableEq

/-! ## Node kind -/

/-- The kind tag for a node, used for kind-compatibility checks. -/
inductive NodeKind where
  | plainObject
  | array
  | date
  | map
  | set
  | arrayBuffer
  | dataView
  | typedArray
deriving DecidableEq, Repr

/-- Extract the kind tag from a node. -/
def Node.kind {A : Type} {ι : Type} : Node A ι → NodeKind
  | .plainObject .. => .plainObject
  | .array ..       => .array
  | .date ..        => .date
  | .map ..         => .map
  | .set ..         => .set
  | .arrayBuffer .. => .arrayBuffer
  | .dataView ..    => .dataView
  | .typedArray ..  => .typedArray

variable {A : Type} {ι : Type}

@[simp] theorem Node.kind_plainObject {p : ProtoLabel} {f : ObjFields A ι} :
    (Node.plainObject p f).kind = .plainObject := rfl
@[simp] theorem Node.kind_array {e : List (Option (Value A ι))} :
    (Node.array e).kind = .array := rfl
@[simp] theorem Node.kind_date {m : Int} :
    (Node.date m : Node A ι).kind = .date := rfl
@[simp] theorem Node.kind_map {e : List (Value A ι × Value A ι)} :
    (Node.map e).kind = .map := rfl
@[simp] theorem Node.kind_set {v : List (Value A ι)} :
    (Node.set v).kind = .set := rfl
@[simp] theorem Node.kind_arrayBuffer {b : List UInt8} :
    (Node.arrayBuffer b : Node A ι).kind = .arrayBuffer := rfl
@[simp] theorem Node.kind_dataView {r : ι} {o l : Nat} :
    (Node.dataView r o l : Node A ι).kind = .dataView := rfl
@[simp] theorem Node.kind_typedArray {t : CtorTag} {r : ι} {o l : Nat}
    {e : List (Value A ι)} :
    (Node.typedArray t r o l e).kind = .typedArray := rfl

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

/-- Plain-object fields are well-formed when keys are duplicate-free. -/
def ObjFieldsWF {A : Type} {ι : Type} (fields : ObjFields A ι) : Prop :=
  fields.NodupKeys

/-- A map entry sequence is well-formed if keys are pairwise related by the
    abstract key-equivalence relation (no duplicate keys). We parameterize by
    a decidable key-equivalence to stay JS-free. -/
structure MapWF (A : Type) (ι : Type)
    (keyEq : Value A ι → Value A ι → Prop) [DecidableRel keyEq] where
  entries : List (Value A ι × Value A ι)
  nodupKeys : entries.Pairwise (fun a b => ¬ keyEq a.1 b.1)

/-- A set value sequence is well-formed if values are pairwise related by the
    abstract value-equivalence relation (no duplicates). -/
structure SetWF (A : Type) (ι : Type)
    (valEq : Value A ι → Value A ι → Prop) [DecidableRel valEq] where
  values : List (Value A ι)
  nodupVals : values.Pairwise (fun a b => ¬ valEq a b)

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

/-! ## Witness maps (for reconcile) -/

/-- Reuse witness: maps consumed current nodes to the next node they are
    aligned against. -/
abbrev ReuseMap := Finmap (fun _ : CurId => NextId)

/-- Image witness: maps next nodes to their canonical result image. -/
abbrev ImageMap := Finmap (fun _ : NextId => ResId)

end Reconcile
