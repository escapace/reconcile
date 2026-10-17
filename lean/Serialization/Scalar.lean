import Serialization.Codec

namespace SerializationScalar

structure Number where
  numerator : Int
  denominator : Nat
  positive : 0 < denominator
  deriving DecidableEq

inductive Value (n : Nat) where
  | number : Number → Value n
  | ref : Fin n → Value n
  | special : Fin 5 → Value n
  | bigint : String → Value n
  | literal : String → Value n
  deriving DecidableEq

-- Distinct constructors correspond to JSON scalar versus tagged array contexts.
inductive Wire where
  | scalar : Number → Wire
  | escapedNegative : Number → Wire
  | special : Fin 5 → Wire
  | bigint : String → Wire
  | literal : String → Wire
  deriving DecidableEq

def referenceNumber (id : Nat) : Number := ⟨-((id : Int) + 1), 1, by decide⟩

def encode {n : Nat} : Value n → Wire
  | .number x => if x.numerator < 0 then .escapedNegative x else .scalar x
  | .ref i => .scalar (referenceNumber i.val)
  | .special s => .special s
  | .bigint s => .bigint s
  | .literal s => .literal s

def decode (n : Nat) : Wire → Option (Value n)
  | .scalar x =>
    if x.numerator < 0 then
      if x.denominator = 1 then
        (SerializationLab.decodeRef n (-x.numerator - 1).toNat).map Value.ref
      else none
    else some (.number x)
  | .escapedNegative x => if x.numerator < 0 then some (.number x) else none
  | .special s => some (.special s)
  | .bigint s => some (.bigint s)
  | .literal s => some (.literal s)

theorem reference_negative (i : Nat) : (referenceNumber i).numerator < 0 := by
  simp only [referenceNumber]
  omega

theorem reference_index (i : Nat) : (-(referenceNumber i).numerator - 1).toNat = i := by
  simp [referenceNumber]

theorem reference_injective : Function.Injective referenceNumber := by
  intro i j h
  have hn := congrArg Number.numerator h
  simp only [referenceNumber] at hn
  omega

theorem decode_encode {n : Nat} (v : Value n) : decode n (encode v) = some v := by
  cases v with
  | number x =>
    by_cases h : x.numerator < 0 <;> simp [encode, decode, h]
  | ref i => simp [encode, decode, referenceNumber,
      SerializationLab.decodeRef, i.isLt]
  | special s => rfl
  | bigint s => rfl
  | literal s => rfl

theorem encode_injective {n : Nat} : Function.Injective (encode (n := n)) := by
  intro a b h
  have hd := congrArg (decode n) h
  simpa only [decode_encode, Option.some.injEq] using hd

theorem number_ref_distinct {n : Nat} (x : Number) (i : Fin n) :
    encode (Value.number x : Value n) ≠ encode (.ref i) := by
  intro h
  have := encode_injective h
  contradiction

theorem escaped_scalar_distinct (x y : Number) : Wire.escapedNegative x ≠ .scalar y := by
  intro h
  cases h

theorem reference_out_of_bounds (n i : Nat) (h : n ≤ i) :
    decode n (.scalar (referenceNumber i)) = none := by
  simp [decode, referenceNumber,
    SerializationLab.decodeRef, show ¬ i < n by omega]

theorem fractional_negative_rejected (n : Nat) (x : Number)
    (hn : x.numerator < 0) (hd : x.denominator ≠ 1) :
    decode n (.scalar x) = none := by simp [decode, hn, hd]

theorem nonnegative_escape_rejected (n : Nat) (x : Number) (h : ¬ x.numerator < 0) :
    decode n (.escapedNegative x) = none := by simp [decode, h]

-- Context matters: ordinary negative payload -1 is escaped, reference zero is scalar -1.
example : encode (Value.number ⟨-1, 1, by decide⟩ : Value 1) =
    .escapedNegative ⟨-1, 1, by decide⟩ := by decide
example : encode (Value.ref ⟨0, by decide⟩ : Value 1) =
    .scalar ⟨-1, 1, by decide⟩ := by decide
example : encode (Value.number ⟨-1, 2, by decide⟩ : Value 0) =
    .escapedNegative ⟨-1, 2, by decide⟩ := by decide

#print axioms reference_negative
#print axioms reference_index
#print axioms reference_injective
#print axioms decode_encode
#print axioms encode_injective
#print axioms number_ref_distinct
#print axioms escaped_scalar_distinct
#print axioms reference_out_of_bounds
#print axioms fractional_negative_rejected
#print axioms nonnegative_escape_rejected

end SerializationScalar
