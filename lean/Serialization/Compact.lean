import Serialization.Scalar
namespace CompactScalar
open SerializationScalar
inductive Layout where | integers | halves deriving DecidableEq

def offset : Layout → Nat | .integers => 6 | .halves => 1

def reference (layout : Layout) (id : Nat) : Number :=
  ⟨-((id : Int) + offset layout), 1, by decide⟩

def special (layout : Layout) (id : Fin 5) : Number :=
  match layout with
  | .integers => ⟨-((id.val : Int) + 1), 1, by decide⟩
  | .halves => ⟨-(2 * (id.val : Int) + 1), 2, by decide⟩

def classify (layout : Layout) (x : Number) : Option (Fin 5) :=
  if x = special layout ⟨0, by decide⟩ then some ⟨0, by decide⟩ else
  if x = special layout ⟨1, by decide⟩ then some ⟨1, by decide⟩ else
  if x = special layout ⟨2, by decide⟩ then some ⟨2, by decide⟩ else
  if x = special layout ⟨3, by decide⟩ then some ⟨3, by decide⟩ else
  if x = special layout ⟨4, by decide⟩ then some ⟨4, by decide⟩ else none

inductive Wire where
  | scalar : Number → Wire
  | escapedNegative : Number → Wire
  | bigint : String → Wire
  | literal : String → Wire
  | legacySingleton : Fin 5 → Wire
  deriving DecidableEq

def encode {n : Nat} (layout : Layout) : Value n → Wire
  | .number x => if x.numerator < 0 then .escapedNegative x else .scalar x
  | .ref id => .scalar (reference layout id.val)
  | .special id => .scalar (special layout id)
  | .bigint text => .bigint text
  | .literal text => .literal text

def decode (layout : Layout) (n : Nat) : Wire → Option (Value n)
  | .scalar x =>
    if x.numerator < 0 then
      match classify layout x with
      | some id => some (.special id)
      | none =>
        if x.denominator = 1 ∧ x.numerator ≤ -(offset layout : Int) then
          (SerializationLab.decodeRef n (-x.numerator - offset layout).toNat).map Value.ref
        else none
    else some (.number x)
  | .escapedNegative x => if x.numerator < 0 then some (.number x) else none
  | .bigint text => some (.bigint text)
  | .literal text => some (.literal text)
  | .legacySingleton _ => none

theorem classify_special (layout : Layout) (id : Fin 5) :
    classify layout (special layout id) = some id := by
  rcases id with ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with h | h | h | h | h <;> subst i <;> cases layout <;> decide +revert

theorem special_negative (layout : Layout) (id : Fin 5) : (special layout id).numerator < 0 := by
  cases layout <;> simp only [special] <;> omega

theorem reference_negative (layout : Layout) (id : Nat) : (reference layout id).numerator < 0 := by
  cases layout <;> simp only [reference, offset] <;> omega

theorem reference_not_special (layout : Layout) (id : Nat) (s : Fin 5) :
    reference layout id ≠ special layout s := by
  intro equal
  cases layout with
  | integers =>
    have h := congrArg Number.numerator equal
    simp only [reference, offset, special] at h
    have := s.isLt
    omega
  | halves =>
    have h := congrArg Number.denominator equal
    simp [reference, special] at h

theorem classify_reference (layout : Layout) (id : Nat) :
    classify layout (reference layout id) = none := by
  simp [classify, reference_not_special]

theorem reference_index (layout : Layout) (id : Nat) :
    (-(reference layout id).numerator - offset layout).toNat = id := by
  simp [reference]

theorem reference_bound (layout : Layout) (id : Nat) :
    (reference layout id).denominator = 1 ∧
      (reference layout id).numerator ≤ -(offset layout : Int) := by
  constructor
  · rfl
  · simp only [reference]
    omega

theorem decode_encode {n : Nat} (layout : Layout) (value : Value n) :
    decode layout n (encode layout value) = some value := by
  cases value with
  | number x => by_cases h : x.numerator < 0 <;> simp [encode, decode, h]
  | ref id =>
    simp only [encode, decode, if_pos (reference_negative layout id.val), classify_reference,
      if_pos (reference_bound layout id.val), reference_index]
    simp [SerializationLab.decodeRef]
  | special id => simp [encode, decode, special_negative, classify_special]
  | bigint text => rfl
  | literal text => rfl

theorem encode_injective {n : Nat} (layout : Layout) : Function.Injective (encode (n := n) layout) := by
  intro a b equal
  have h := congrArg (decode layout n) equal
  simpa only [decode_encode, Option.some.injEq] using h

theorem reference_out_of_bounds (layout : Layout) (n id : Nat) (invalid : n ≤ id) :
    decode layout n (.scalar (reference layout id)) = none := by
  simp only [decode, if_pos (reference_negative layout id), classify_reference,
    if_pos (reference_bound layout id), reference_index]
  simp [SerializationLab.decodeRef, show ¬ id < n by omega]

theorem legacy_rejected (layout : Layout) (n : Nat) (id : Fin 5) :
    decode layout n (.legacySingleton id) = none := rfl

-- The actual node table is a native array; neither layout adds a policy quota.
theorem native_reference_exact_range (layout : Layout) (id : Nat) (bound : id < 4294967295) :
    id + offset layout < 9007199254740992 := by
  cases layout <;> simp only [offset] <;> omega

-- Explicit JSON tree shapes: negative data and bigint tags stay in arrays;
-- special values and references now occupy scalar number positions.
inductive JSON where
  | number : Number → JSON
  | string : String → JSON
  | array : List JSON → JSON

def tagNumber (value : Int) : Number := ⟨value, 1, by decide⟩
def toJSON : Wire → JSON
  | .scalar x => .number x
  | .literal text => .string text
  | .escapedNegative x => .array [.number (tagNumber (-7)), .number x]
  | .bigint text => .array [.number (tagNumber (-6)), .string text]
  | .legacySingleton id => .array [.number (special .integers id)]
def fromJSON : JSON → Option Wire
  | .number x => some (.scalar x)
  | .string text => some (.literal text)
  | .array [.number tag, .number x] =>
    if tag = tagNumber (-7) then some (.escapedNegative x) else none
  | .array [.number tag, .string text] =>
    if tag = tagNumber (-6) then some (.bigint text) else none
  | .array [.number tag] => (classify .integers tag).map Wire.legacySingleton
  | _ => none

theorem json_tree_roundtrip (wire : Wire) : fromJSON (toJSON wire) = some wire := by
  cases wire with
  | scalar x => rfl
  | literal text => rfl
  | escapedNegative x => simp [toJSON, fromJSON]
  | bigint text => simp [toJSON, fromJSON]
  | legacySingleton id => simp [toJSON, fromJSON, classify_special]

theorem json_value_roundtrip {n : Nat} (layout : Layout) (value : Value n) :
    (fromJSON (toJSON (encode layout value))).bind (decode layout n) = some value := by
  rw [json_tree_roundtrip]
  exact decode_encode layout value

theorem json_image_injective {n : Nat} (layout : Layout) :
    Function.Injective (fun value : Value n => toJSON (encode layout value)) := by
  intro a b equal
  have h := congrArg (fun json => (fromJSON json).bind (decode layout n)) equal
  simpa only [json_value_roundtrip, Option.some.injEq] using h

theorem special_index (layout : Layout) (id : Fin 5) :
    (if layout = .integers then (-(special layout id).numerator - 1).toNat
     else ((-(special layout id).numerator - 1) / 2).toNat) = id.val := by
  cases layout <;> simp [special]

#print axioms json_tree_roundtrip
#print axioms json_value_roundtrip
#print axioms json_image_injective
#print axioms special_index
#print axioms classify_special
#print axioms special_negative
#print axioms reference_negative
#print axioms reference_not_special
#print axioms classify_reference
#print axioms reference_index
#print axioms reference_bound
#print axioms decode_encode
#print axioms encode_injective
#print axioms reference_out_of_bounds
#print axioms legacy_rejected
#print axioms native_reference_exact_range
end CompactScalar
