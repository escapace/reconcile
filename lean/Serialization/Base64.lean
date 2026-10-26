import Mathlib.Data.List.Basic

/-!
# Table-driven base64 encoding

RFC 4648 §4 encodes each group of three bytes as four 6-bit values, high bits first; a final
group of one or two bytes is completed with zero bits, and the missing values become padding.
`sextets` states that definition bytewise. The runtime packs a group into one 24-bit word and
reads its four 6-bit fields by shifts and masks (`fields`), then maps each value through the
64-entry alphabet. This file proves:

* the word fields are the bytewise sextets whenever the two low bytes are bytes
  (`fields_sextets`);
* the runtime's loop over a byte list, including its one- and two-byte final groups, emits
  exactly the specification (`encode_spec`);
* the output has four values per started group (`encode_length`).

Values are alphabet indices, with `pad` for `=`. That the alphabet maps index i to the i-th
character of `A–Z a–z 0–9 + /`, that `>>`, `&` and `|` on these nonnegative words agree with the
division and remainder used here, and that the ASCII bytes decode to the same string, are
runtime obligations; the bridge compares the runtime encoder with the native `btoa`.
-/

namespace SerializationBase64

/-- The padding value, outside the alphabet's indices. -/
def pad : Nat := 64

/-- RFC 4648: the four 6-bit values of bytes `a b c`, high bits first. -/
def sextets (a b c : Nat) : List Nat :=
  [a / 4, a % 4 * 16 + b / 16, b % 16 * 4 + c / 64, c % 64]

/-- The specification: whole groups, then a final group completed with zero bits. -/
def spec : List Nat → List Nat
  | a :: b :: c :: rest => sextets a b c ++ spec rest
  | [a, b] => (sextets a b 0).take 3 ++ [pad]
  | [a] => (sextets a 0 0).take 2 ++ [pad, pad]
  | [] => []

/-- The runtime's packed group and its four fields. -/
def word (a b c : Nat) : Nat := a * 65536 + b * 256 + c

def fields (v : Nat) : List Nat := [v / 262144, v / 4096 % 64, v / 64 % 64, v % 64]

theorem fields_sextets {a b c : Nat} (hb : b < 256) (hc : c < 256) :
    fields (word a b c) = sextets a b c := by
  simp only [fields, sextets, word, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The runtime loop: whole groups from packed words; a final group of two bytes keeps three
fields, of one byte two, each followed by padding. -/
def encode : List Nat → List Nat
  | a :: b :: c :: rest => fields (word a b c) ++ encode rest
  | [a, b] => (fields (word a b 0)).take 3 ++ [pad]
  | [a] => (fields (word a 0 0)).take 2 ++ [pad, pad]
  | [] => []

theorem encode_spec : ∀ bytes : List Nat, (∀ x ∈ bytes, x < 256) → encode bytes = spec bytes
  | a :: b :: c :: rest, h => by
    simp only [encode, spec]
    rw [fields_sextets (h b (by simp)) (h c (by simp)),
      encode_spec rest (fun x hx => h x (by simp [hx]))]
  | [a, b], h => by
    simp only [encode, spec]
    rw [fields_sextets (h b (by simp)) (by omega)]
  | [a], h => by
    simp only [encode, spec]
    rw [fields_sextets (by omega) (by omega)]
  | [], _ => rfl

theorem encode_length : ∀ bytes : List Nat, (encode bytes).length = 4 * ((bytes.length + 2) / 3)
  | _ :: _ :: _ :: rest => by
    have := encode_length rest
    simp only [encode, List.length_append, fields, List.length_cons, List.length_nil] at this ⊢
    omega
  | [_, _] => by simp [encode, fields]
  | [_] => by simp [encode, fields]
  | [] => rfl

example : encode [77, 97, 110] = [19, 22, 5, 46] := by decide
example : encode [77, 97] = [19, 22, 4, pad] := by decide
example : encode [77] = [19, 16, pad, pad] := by decide

end SerializationBase64
