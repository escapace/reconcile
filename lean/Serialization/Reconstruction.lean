import Serialization.Codec
import Mathlib.Data.List.Nodup

namespace SerializationV9
open SerializationLab

-- No format identifier: only these three context-specific components remain.
structure Document where
  root : Token Nat
  shapes : List (List String)
  nodes : List (Node Nat)

def tokenValid (n : Nat) : Token Nat → Bool
  | .atom _ => true
  | .ref i => decide (i < n)

theorem token_valid_iff_decode (n : Nat) (token : Token Nat) :
    tokenValid n token = true ↔ (decodeToken n token).isSome = true := by
  cases token with
  | atom a => rfl
  | ref i => by_cases h : i < n <;> simp [tokenValid, decodeToken, decodeRef, h]

def resolve {n : Nat} {Handle : Type} (allocated : Fin n → Handle) (id : Nat) : Option Handle :=
  (decodeRef n id).map allocated

theorem resolve_allocated {n : Nat} {Handle : Type} (allocated : Fin n → Handle) (id : Fin n) :
    resolve allocated id.val = some (allocated id) := by simp [resolve]

theorem resolve_identity {n : Nat} {Handle : Type} (allocated : Fin n → Handle)
    (fresh : Function.Injective allocated) (i j : Fin n) :
    resolve allocated i.val = resolve allocated j.val ↔ i = j := by
  simp only [resolve_allocated, Option.some.injEq]
  exact fresh.eq_iff

def shapeValid (shapes : List (List String)) (id : Nat) : Bool :=
  match shapes[id]? with
  | none => false
  | some keys => decide keys.Nodup

def shapeCheck (shapes : List (List String)) (checked : List Nat) (id : Nat) : Bool :=
  if id ∈ checked then true else shapeValid shapes id

def CheckedSound (shapes : List (List String)) (checked : List Nat) : Prop :=
  ∀ i ∈ checked, shapeValid shapes i = true

theorem cached_shape_check_exact (shapes : List (List String)) (checked : List Nat) (id : Nat)
    (sound : CheckedSound shapes checked) : shapeCheck shapes checked id = shapeValid shapes id := by
  by_cases h : id ∈ checked
  · simp [shapeCheck, h, sound id h]
  · simp [shapeCheck, h]

theorem remember_shape_sound (shapes : List (List String)) (checked : List Nat) (id : Nat)
    (sound : CheckedSound shapes checked) (valid : shapeValid shapes id = true) :
    CheckedSound shapes (id :: checked) := by
  intro i hi
  rcases List.mem_cons.mp hi with h | h
  · simpa [h] using valid
  · exact sound i h

def recordEdges (doc : Document) (shape : Nat) (values : List (Token Nat)) :=
  dictionaryExpand doc.shapes shape values

theorem record_exact (doc : Document) (shape : Nat) (edges : List (String × Token Nat))
    (selected : doc.shapes[shape]? = some (edges.map Prod.fst)) :
    recordEdges doc shape (edges.map Prod.snd) = some edges :=
  dictionary_exact doc.shapes shape edges selected

def linkView {Handle : Type} (nodes : List (Node Nat))
    (allocated : Fin nodes.length → Handle) (id : Nat) : Option Handle :=
  if h : id < nodes.length then
    if nodes[id].kind = .buffer then some (allocated ⟨id, h⟩) else none
  else none

theorem view_link_requires_buffer {Handle : Type} (nodes : List (Node Nat))
    (allocated : Fin nodes.length → Handle) (id : Nat) (handle : Handle)
    (h : linkView nodes allocated id = some handle) :
    ∃ i : Fin nodes.length, i.val = id ∧ nodes[i.val].kind = .buffer ∧ allocated i = handle := by
  unfold linkView at h
  split at h
  · rename_i bound
    split at h
    · rename_i kind
      exact ⟨⟨id, bound⟩, rfl, kind, Option.some.inj h⟩
    · contradiction
  · contradiction

theorem view_extent_bound (length offset count unit : Nat) (offset_ok : offset ≤ length)
    (count_ok : count ≤ (length - offset) / unit) : offset + count * unit ≤ length := by
  have hm := (Nat.mul_le_mul_right unit count_ok).trans (Nat.div_mul_le_self (length - offset) unit)
  omega

structure Sparse (α : Type) where
  length : Nat
  slot : Nat → Option α

def allocatedSparse {α : Type} (length : Nat) : Sparse α := ⟨length, fun _ => none⟩
def resize {α : Type} (array : Sparse α) (length : Nat) : Sparse α :=
  ⟨length, fun i => if i < length then array.slot i else none⟩

theorem empty_resize_exact {α : Type} (length : Nat) :
    resize (allocatedSparse (α := α) 0) length = allocatedSparse length := by
  simp [resize, allocatedSparse]

def write {α : Type} (array : Sparse α) (index : Nat) (value : α) : Option (Sparse α) :=
  if index < array.length then
    some ⟨array.length, fun i => if i = index then some value else array.slot i⟩
  else none

theorem write_length {α : Type} (array result : Sparse α) (index : Nat) (value : α)
    (h : write array index value = some result) : result.length = array.length := by
  unfold write at h
  split at h <;> cases h
  rfl

theorem write_presence {α : Type} (array : Sparse α) (index : Nat) (value : α)
    (bound : index < array.length) :
    (write array index value).map (fun result => result.slot index) = some (some value) := by
  simp [write, bound]

theorem write_other {α : Type} (array : Sparse α) (index other : Nat) (value : α)
    (bound : index < array.length) (distinct : other ≠ index) :
    (write array index value).map (fun result => result.slot other) = some (array.slot other) := by
  simp [write, bound, distinct]

def fill {α : Type} : Sparse α → List (Nat × α) → Option (Sparse α)
  | array, [] => some array
  | array, (index, value) :: rest => (write array index value).bind (fun next => fill next rest)

theorem fill_length {α : Type} (pairs : List (Nat × α)) (array result : Sparse α)
    (h : fill array pairs = some result) : result.length = array.length := by
  induction pairs generalizing array with
  | nil => simpa [fill] using (congrArg (Option.map Sparse.length) h).symm
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    simp only [fill] at h
    cases hw : write array index value with
    | none => simp [hw] at h
    | some next =>
      simp only [hw, Option.bind_some] at h
      exact (ih next h).trans (write_length array next index value hw)

theorem sparse_fill_same {α : Type} (length : Nat) (pairs : List (Nat × α)) :
    fill (resize (allocatedSparse 0) length) pairs = fill (allocatedSparse length) pairs := by
  rw [empty_resize_exact]

example : (write (allocatedSparse (α := Option Nat) 3) 1 none).map (fun a => a.slot 1) =
    some (some none) := by decide
example : (allocatedSparse (α := Option Nat) 3).slot 1 = none := rfl

#print axioms token_valid_iff_decode
#print axioms resolve_allocated
#print axioms resolve_identity
#print axioms cached_shape_check_exact
#print axioms remember_shape_sound
#print axioms record_exact
#print axioms view_link_requires_buffer
#print axioms view_extent_bound
#print axioms empty_resize_exact
#print axioms write_length
#print axioms write_presence
#print axioms write_other
#print axioms fill_length
#print axioms sparse_fill_same

end SerializationV9
